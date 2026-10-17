(** Finite administrative unfoldings; recursion is not evaluated here. *)
From CaseStudy Require Import NatArithmetic ArithmeticProofTools.
From ContextTyping Require Import Conversion.
From CoreLang Require Import InstantiationProps.
From Denotation Require Import TypeEquivTermBase.
From ContextBasicDenotation Require Import TermSyntax.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.

Definition arithmetic_value (is_add : bool) : value :=
  match is_add with true => NatArithmetic.add_value | false => NatArithmetic.sub_value end.
Definition arithmetic_function (is_add : bool) : nat -> nat -> nat :=
  match is_add with true => Nat.add | false => Nat.sub end.

Definition arithmetic_partial is_add vx : value :=
  match arithmetic_value is_add with
  | vfix _ (vlam _ (tret v)) =>
      open_value 0 (arithmetic_value is_add) (open_value 1 vx v)
  | _ => vconst cunit
  end.
Definition arithmetic_body is_add vx vy : tm :=
  match arithmetic_partial is_add vx with
  | vlam _ body => open_tm 0 vy body
  | _ => tret (vconst cunit)
  end.

Inductive arithmetic_prefix : tm -> tm -> Prop :=
| Prefix_refl e : arithmetic_prefix e e
| Prefix_step e e' e'' :
    (step e e' /\ forall z, step e z -> z = e') ->
    arithmetic_prefix e' e'' -> arithmetic_prefix e e''.

Lemma arithmetic_prefix_equivalence e e' :
  arithmetic_prefix e e' ->
  (forall v, e →* tret v <-> e' →* tret v) /\
  (must_terminating e <-> must_terminating e').
Proof.
  induction 1 as [e|e e' e'' [Hs Hd] Hp [IHv IHtotal]].
  - split; [intros; reflexivity|reflexivity].
  - destruct (deterministic_step_equivalence e e' Hs Hd) as [Hv Ht].
    split; [intros v; rewrite Hv; apply IHv|rewrite Ht; exact IHtotal].
Qed.

Ltac arithmetic_prefix_steps :=
  first [apply Prefix_refl|
    lazymatch goal with |- arithmetic_prefix ?e ?target =>
      let e' := eval vm_compute in e in
      change (arithmetic_prefix e' target);
      eapply Prefix_step; [arithmetic_certify_step|arithmetic_prefix_steps]
    end].

Lemma arithmetic_partial_prefix is_add n :
  arithmetic_prefix
    (tapp_tm (tret (arithmetic_value is_add)) (vnat n))
    (tret (arithmetic_partial is_add (vnat n))).
Proof. destruct is_add; arithmetic_prefix_steps. Qed.

Lemma arithmetic_body_prefix is_add n k :
  arithmetic_prefix
    (NatArithmetic.app2 (arithmetic_value is_add) (vnat n) (vnat k))
    (arithmetic_body is_add (vnat n) (vnat k)).
Proof. destruct is_add; arithmetic_prefix_steps. Qed.

Definition arithmetic_lam_body is_add vx : tm :=
  match arithmetic_partial is_add vx with
  | vlam _ body => body
  | _ => tret (vconst cunit)
  end.

Lemma arithmetic_partial_lam is_add vx :
  arithmetic_partial is_add vx = vlam TNat (arithmetic_lam_body is_add vx).
Proof. destruct is_add; reflexivity. Qed.
Lemma arithmetic_body_open is_add vx vy :
  arithmetic_body is_add vx vy = open_tm 0 vy (arithmetic_lam_body is_add vx).
Proof. destruct is_add; reflexivity. Qed.

Lemma arithmetic_value_typed is_add Δ :
  value_has_type Δ (arithmetic_value is_add) nat_binop_ty.
Proof.
  destruct is_add; eapply basic_typing_weaken_value;
    [apply add_value_basic_typed|apply map_empty_subseteq|apply sub_value_basic_typed|apply map_empty_subseteq].
Qed.
