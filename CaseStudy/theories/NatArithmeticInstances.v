(** Natural-input instances, derived by syntactic induction. *)
From CaseStudy Require Import NatArithmetic.
From CoreLang Require Import Sugar BasicTypingProps SmallStep OperationalProps StrongNormalization.
From ContextTyping Require Import Typing NatCases Conversion.
Local Ltac arith_atoms G :=
  lazymatch G with
  | <[?x := _]> ?G' =>
      let L := arith_atoms G' in constr:({[x]} ∪ L : aset)
  | _ => constr:(∅ : aset)
  end.

Local Ltac lookup_arith_var :=
  lazymatch goal with
  | |- (<[?x := _]> _) !! ?y = _ =>
      tryif constr_eq x y then apply lookup_insert_eq else
      rewrite lookup_insert_ne by set_solver; lookup_arith_var
  | |- _ => fail "Arithmetic variable is missing from the basic typing context"
  end.

Local Ltac type_arith :=
  lazymatch goal with
  | |- tm_has_type ?G ?e ?T =>
      let e' := eval vm_compute in e in change (tm_has_type G e' T)
  | |- value_has_type ?G ?v ?T =>
      let v' := eval vm_compute in v in change (value_has_type G v' T)
  end;
  lazymatch goal with
  | |- tm_has_type _ (tret _) _ => apply TT_Ret; type_arith
  | |- tm_has_type ?G (tlete _ _) _ =>
      let atoms := arith_atoms G in
      eapply TT_Let with (L := atoms);
      [type_arith | let x := fresh "x" in let Hx := fresh "Hx" in
        intros x Hx; type_arith]
  | |- tm_has_type _ (tprim ?op _) _ =>
      let sig := eval cbv in (prim_op_type op) in
      lazymatch sig with
      | (?A, ?B) => eapply TT_Op with (arg_b := A) (ret_b := B);
          [reflexivity | type_arith]
      end
  | |- tm_has_type _ (tapp _ _) _ => eapply TT_App; type_arith
  | |- tm_has_type _ (tmatch _ _ _) _ => apply TT_Match; type_arith
  | |- tm_has_type _ (tnode _ _ _) _ => apply TT_TreeNode; type_arith
  | |- value_has_type _ (vconst _) _ => cbn [base_ty_of_const]; apply VT_Const
  | |- value_has_type _ (vfvar _) _ => apply VT_FVar; lookup_arith_var
  | |- value_has_type ?G (vlam _ _) _ =>
      let atoms := arith_atoms G in
      eapply VT_Lam with (L := atoms);
      let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; type_arith
  | |- value_has_type ?G (vfix _ _) _ =>
      let atoms := arith_atoms G in
      eapply VT_Fix with (L := atoms);
      let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; type_arith
  | |- _ => fail "Unsupported Arithmetic basic typing goal"
  end.

Local Lemma arithmetic_head_deterministic e e' :
  head_step e e' ->
  (forall op c, e = tprim op (vconst c) ->
    op <> op_boolGen /\ op <> op_natGen) ->
  forall z, step e z -> z = e'.
Proof.
  intros Hhead Hops z Hz.
  inversion Hz; subst.
  - inversion Hhead; subst; inversion H; subst; try reflexivity.
    match goal with
    | Hp : prim_step ?op ?c ?c' |- _ =>
        destruct (Hops op c eq_refl) as [Hb Hn];
        inversion Hp; subst; try contradiction;
        match goal with Hp' : prim_step _ _ _ |- _ =>
          inversion Hp'; subst; reflexivity end
    end.
  - inversion Hhead; subst. exfalso. eapply val_no_step; eauto.
Qed.

Local Ltac arithmetic_lc :=
  eapply (basic_typing_regular_tm ∅); type_arith.

Local Ltac arithmetic_head :=
  first [apply HS_Ret | apply HS_Beta | apply HS_Fix |
    apply HS_MatchTrue | apply HS_MatchFalse |
    (apply HS_Op; [constructor|])]; arithmetic_lc.

(** Context typing of each closed natural-input instance.  These are
    syntax derivations by induction, independently of [add_value_run] and
    [sub_value_run].  The recursive premise is the induction hypothesis. *)
Local Lemma arithmetic_certified_let e e' body :
  (step e e' /\ forall z, step e z -> z = e') ->
  lc_tm (tlete e body) ->
  step (tlete e body) (tlete e' body) /\
    forall z, step (tlete e body) z -> z = tlete e' body.
Proof.
  intros [Hs Hd] Hlc. split; [apply Step_let; assumption|].
  intros z Hz. inversion Hz; subst.
  - match goal with Hh : head_step _ _ |- _ => inversion Hh; subst end.
    exfalso. eapply val_no_step; exact Hs.
  - match goal with Hs' : step e ?z' |- _ => rewrite (Hd z' Hs') end.
    reflexivity.
Qed.

Local Ltac arithmetic_certify_step :=
  lazymatch goal with
  | |- step (tlete (tret _) _) _ /\ _ =>
      split; [apply Step_head; arithmetic_head|
        eapply arithmetic_head_deterministic;
        [arithmetic_head|intros op c H; discriminate]]
  | |- step (tlete _ _) _ /\ _ =>
      apply arithmetic_certified_let; [arithmetic_certify_step|arithmetic_lc]
  | |- step _ _ /\ _ =>
      split; [apply Step_head; arithmetic_head|
        eapply arithmetic_head_deterministic;
        [arithmetic_head|intros op c H; inversion H; subst; split; discriminate]]
  end.

Local Ltac arithmetic_instance_wf :=
  split; [constructor|]; split; [apply nat_singleton_wf|]; type_arith.

Local Ltac type_arithmetic_instance IH :=
  first [apply IH |
    lazymatch goal with
    | |- has_context_type _ _ _ (tret _) _ =>
        apply CT_Const; arithmetic_instance_wf
    | |- has_context_type ?F ?S ?G ?e ?T =>
        let e' := eval vm_compute in e in
        change (has_context_type F S G e' T);
        eapply typing_closed_deterministic_step;
        [arithmetic_instance_wf | arithmetic_certify_step |
         vm_compute; reflexivity | vm_compute; reflexivity |
         type_arithmetic_instance IH]
    end].

Theorem add_instance_typing Φ n m :
  has_context_type Φ ∅ CtxEmpty
    (NatArithmetic.app2 NatArithmetic.add_value (vnat n) (vnat m))
    (nat_singleton_ty (n + m)).
Proof.
  revert m. induction n as [|n IH]; intros m.
  - type_arithmetic_instance IH.
  - replace (S n + m) with (n + S m) by lia.
    type_arithmetic_instance IH.
Qed.

Theorem sub_instance_typing Φ n m :
  has_context_type Φ ∅ CtxEmpty
    (NatArithmetic.app2 NatArithmetic.sub_value (vnat n) (vnat m))
    (nat_singleton_ty (n - m)).
Proof.
  revert m. induction n as [|n IH]; intros [|m].
  - type_arithmetic_instance IH.
  - type_arithmetic_instance IH.
  - rewrite Nat.sub_0_r. type_arithmetic_instance IH.
  - type_arithmetic_instance IH.
Qed.
