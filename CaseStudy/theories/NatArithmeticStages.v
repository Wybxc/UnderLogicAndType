From CaseStudy Require Export NatArithmeticUnfolding ArithmeticProofTools.
(** Finite administrative unfoldings; recursion is not evaluated here. *)
From CaseStudy Require Import NatArithmetic ArithmeticProofTools.
From ContextTyping Require Import Conversion.
From CoreLang Require Import InstantiationProps.
From Denotation Require Import TypeEquivTermBase.
From ContextBasicDenotation Require Import TermSyntax.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.

Ltac arithmetic_closed_value ::=
  lazymatch goal with
  | |- value_has_type ?Δ ?v ?T =>
      first [eapply (basic_typing_weaken_value ∅ Δ v T);
        [exact add_value_basic_typed|apply map_empty_subseteq] |
        eapply (basic_typing_weaken_value ∅ Δ v T);
        [exact sub_value_basic_typed|apply map_empty_subseteq]]
  end.

Lemma arithmetic_partial_typed is_add Δ x :
  Δ !! x = Some (TBase TNat) ->
  value_has_type Δ (arithmetic_partial is_add (vfvar x)) (TNat →ᵦ TNat).
Proof.
  intros Hx. assert (Hxdom : x ∈ dom Δ) by (apply elem_of_dom; eauto).
  destruct is_add; type_arith.
Qed.

Lemma arithmetic_body_typed is_add Δ x y :
  Δ !! x = Some (TBase TNat) -> Δ !! y = Some (TBase TNat) ->
  tm_has_type Δ (arithmetic_body is_add (vfvar x) (vfvar y)) (TBase TNat).
Proof.
  intros Hx Hy.
  assert (Hxdom : x ∈ dom Δ) by (apply elem_of_dom; eauto).
  assert (Hydom : y ∈ dom Δ) by (apply elem_of_dom; eauto).
  destruct is_add; type_arith.
Qed.

Ltac arithmetic_instantiate :=
  lazymatch goal with
  | |- lstore_instantiate_tm ?σ ?e = ?rhs =>
      let e' := eval vm_compute in e in
      change (lstore_instantiate_tm σ e' = rhs)
  end;
  unfold lstore_instantiate_tm, lstore_instantiate_tm_at;
  rewrite lstore_free_part_lift_free;
  rewrite lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free;
  cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].

Lemma arithmetic_partial_instantiate is_add σ x n :
  σ !! x = Some (vnat n) ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (tret (arithmetic_partial is_add (vfvar x))) =
  tret (arithmetic_partial is_add (vnat n)).
Proof. intros Hx. destruct is_add; arithmetic_instantiate; setoid_rewrite Hx; vm_compute; reflexivity. Qed.

Lemma arithmetic_call_instantiate is_add σ x n :
  σ !! x = Some (vnat n) ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (tapp_tm (tret (arithmetic_value is_add)) (vfvar x)) =
  tapp_tm (tret (arithmetic_value is_add)) (vnat n).
Proof. intros Hx. destruct is_add; arithmetic_instantiate; setoid_rewrite Hx; vm_compute; reflexivity. Qed.

Lemma arithmetic_body_instantiate is_add σ x y n k :
  σ !! x = Some (vnat n) -> σ !! y = Some (vnat k) ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (arithmetic_body is_add (vfvar x) (vfvar y)) =
  arithmetic_body is_add (vnat n) (vnat k).
Proof. intros Hx Hy. destruct is_add; arithmetic_instantiate; setoid_rewrite Hx; setoid_rewrite Hy; vm_compute; reflexivity. Qed.
