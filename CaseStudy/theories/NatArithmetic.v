(** * Natural arithmetic library in the existing unary core language. *)
From CaseStudy Require Export CaseTypes.
From CoreLang Require Import Sugar BasicTypingProps SmallStep OperationalProps
  StrongNormalization.
From ContextTypeLanguage Require Import WF.
Open Scope core_scope.
Open Scope cty_scope.

Module NatArithmetic.

(** Named builders close their binder into the existing locally-nameless
    syntax. All names below are distinct; the resulting exported program
    has no free atoms. Application helpers use capture-avoiding shifting. *)
Definition let_in (x : atom) (rhs body : tm) : tm :=
  tlete rhs (close_tm x 0 body).

Definition lam (x : atom) (T : ty) (body : tm) : value :=
  vlam T (close_tm x 0 body).

Definition fix_fun (self arg : atom) (A B : ty) (body : tm) : value :=
  vfix (TArrow A B)
    (close_value arg 0 (lam self (TArrow A B) body)).

Definition app2 (f a b : value) : tm :=
  tapp_tm (tapp f a) b.

Definition app3 (f a b c : value) : tm :=
  tapp_tm (app2 f a b) c.

Definition choose (left right : tm) : tm :=
  tlete (tprim op_boolGen (vconst cunit))
    (tmatch (vbvar 0) (tm_shift 0 left) (tm_shift 0 right)).

Definition self : atom := 1%positive.
Definition a : atom := 2%positive.
Definition b : atom := 3%positive.
Definition az : atom := 4%positive.
Definition bz : atom := 5%positive.
Definition ap : atom := 6%positive.
Definition bp : atom := 7%positive.

(** add a b = if a = 0 then b else add (a - 1) (b + 1). *)
Definition add_value : value :=
  fix_fun self a TNat (TNat →ᵦ TNat)
    (ret (lam b TNat
      (let_in az (tprim op_eq0 (vfvar a))
        (tmatch (vfvar az) (ret (vfvar b))
          (let_in ap (tprim op_minus1 (vfvar a))
            (let_in bp (tprim op_plus1 (vfvar b))
              (app2 (vfvar self) (vfvar ap) (vfvar bp)))))))).

(** sub a b is natural-number subtraction, truncated at zero. *)
Definition sub_value : value :=
  fix_fun self a TNat (TNat →ᵦ TNat)
    (ret (lam b TNat
      (let_in az (tprim op_eq0 (vfvar a))
        (tmatch (vfvar az) (ret (vnat 0))
          (let_in bz (tprim op_eq0 (vfvar b))
            (tmatch (vfvar bz) (ret (vfvar a))
              (let_in ap (tprim op_minus1 (vfvar a))
                (let_in bp (tprim op_minus1 (vfvar b))
                  (app2 (vfvar self) (vfvar ap) (vfvar bp)))))))))).

End NatArithmetic.

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


Lemma add_value_basic_typed :
  value_has_type ∅ NatArithmetic.add_value nat_binop_ty.
Proof.
  let v := eval vm_compute in NatArithmetic.add_value in
  change (value_has_type ∅ v (TNat →ᵦ TNat →ᵦ TNat)).
  type_arith.
Qed.

Lemma sub_value_basic_typed :
  value_has_type ∅ NatArithmetic.sub_value nat_binop_ty.
Proof.
  let v := eval vm_compute in NatArithmetic.sub_value in
  change (value_has_type ∅ v (TNat →ᵦ TNat →ᵦ TNat)).
  type_arith.
Qed.

Definition q_nat_binop (f : nat -> nat -> nat) (a b result : value)
    : type_qualifier :=
  tqual (lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys result)
    (fun σ => exists na nb : nat,
      denote_lvar_value (lso_store σ) a = Some (vnat na) /\
      denote_lvar_value (lso_store σ) b = Some (vnat nb) /\
      denote_lvar_value (lso_store σ) result = Some (vnat (f na nb))).

Definition nat_binop_context_ty (f : nat -> nat -> nat) : context_ty :=
  □ (ONat → ONat → precise_ty TNat (q_nat_binop f arg1 arg0 ν)).
Definition add_context_ty : context_ty := nat_binop_context_ty Nat.add.
Definition sub_context_ty : context_ty := nat_binop_context_ty Nat.sub.

Lemma nat_binop_context_ty_erasure f :
  erase_ty (nat_binop_context_ty f) = nat_binop_ty.
Proof. reflexivity. Qed.

Lemma nat_binop_context_ty_well_formed f :
  basic_context_ty ∅ (nat_binop_context_ty f).
Proof.
  cbn [basic_context_ty wf_context_ty_at nat_binop_context_ty ONat
    over_ty under_ty precise_ty q_nat_binop qual_vars qual_top_on
    arg0 arg1 vnu lvar_value_keys erase_ty].
  unfold lvars_wf_at.
  repeat split; try reflexivity.
  all: intros [k | x] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.

(** A deterministic execution certificate records every reduction, including
    the fact that no other successor is possible.  Thus it proves must
    termination as well as the exact result. *)
Inductive arithmetic_run : tm -> value -> Prop :=
  | Arithmetic_result v : lc_value v -> arithmetic_run (tret v) v
  | Arithmetic_step e e' v :
      step e e' ->
      (forall e'', step e e'' -> e'' = e') ->
      arithmetic_run e' v -> arithmetic_run e v.

Lemma arithmetic_run_steps e v : arithmetic_run e v -> e →* tret v.
Proof.
  induction 1.
  - constructor. constructor. assumption.
  - econstructor; eauto.
Qed.

Lemma arithmetic_run_terminates e v : arithmetic_run e v -> must_terminating e.
Proof.
  induction 1.
  - apply must_terminating_tret. assumption.
  - apply Must_step.
    + exists e'. assumption.
    + intros z Hz. rewrite (H0 z Hz). assumption.
Qed.

Lemma arithmetic_run_unique e v :
  arithmetic_run e v -> forall w, e →* tret w -> w = v.
Proof.
  induction 1; intros w Hw.
  - apply val_steps_self in Hw. congruence.
  - inversion Hw; subst.
    + exfalso. eapply val_no_step; eauto.
    + match goal with Hs : step e ?z |- _ =>
        pose proof (H0 z Hs) as -> end.
      eauto.
Qed.

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

Local Lemma arithmetic_run_let e1 e2 v w :
  lc_tm (tlete e1 e2) ->
  arithmetic_run e1 v ->
  arithmetic_run (open_tm 0 v e2) w ->
  arithmetic_run (tlete e1 e2) w.
Proof.
  intros Hlc Hrun. revert e2 Hlc w.
  induction Hrun as [v Hval | e e' v Hstep Hdet Hrun IH];
    intros e2 Hlc w Hbody.
  - eapply Arithmetic_step; [apply Step_head, HS_Ret; exact Hlc| |exact Hbody].
    eapply arithmetic_head_deterministic; [apply HS_Ret; exact Hlc|].
    intros op c Hbad. discriminate.
  - eapply Arithmetic_step with (e' := tlete e' e2).
    + apply Step_let; [exact Hstep | exact Hlc].
    + intros z Hz. inversion Hz; subst.
      * match goal with Hh : head_step _ _ |- _ => inversion Hh; subst end.
        exfalso. eapply val_no_step; exact Hstep.
      * match goal with Hs : step e ?z' |- _ =>
          rewrite (Hdet z' Hs); reflexivity end.
    + apply IH; [|exact Hbody].
      eapply step_regular2. apply Step_let; eauto.
Qed.

Local Ltac arithmetic_lc :=
  eapply (basic_typing_regular_tm ∅); type_arith.

Local Ltac arithmetic_head :=
  first [apply HS_Ret | apply HS_Beta | apply HS_Fix |
    apply HS_MatchTrue | apply HS_MatchFalse |
    (apply HS_Op; [constructor|])]; arithmetic_lc.

Local Ltac execute_arithmetic IH :=
  tryif solve [apply IH] then idtac else (
    lazymatch goal with |- arithmetic_run ?e ?v =>
      let e' := eval vm_compute in e in
      change (arithmetic_run e' v)
    end;
    lazymatch goal with
    | |- arithmetic_run (tret _) _ =>
        apply Arithmetic_result;
        eapply (basic_typing_regular_value ∅); type_arith
    | |- arithmetic_run (tlete _ _) _ =>
        eapply arithmetic_run_let;
        [arithmetic_lc | execute_arithmetic IH | execute_arithmetic IH]
    | |- arithmetic_run _ _ =>
        eapply Arithmetic_step;
        [apply Step_head; arithmetic_head |
         eapply arithmetic_head_deterministic;
         [arithmetic_head | intros op c H; inversion H; subst; split; discriminate] |
         execute_arithmetic IH]
    end).

Theorem add_value_run n m :
  arithmetic_run
    (NatArithmetic.app2 NatArithmetic.add_value (vnat n) (vnat m))
    (vnat (n + m)).
Proof.
  revert m. induction n as [|n IH]; intros m.
  - execute_arithmetic IH.
  - replace (S n + m) with (n + S m) by lia.
    execute_arithmetic IH.
Qed.

Theorem sub_value_run n m :
  arithmetic_run
    (NatArithmetic.app2 NatArithmetic.sub_value (vnat n) (vnat m))
    (vnat (n - m)).
Proof.
  revert m. induction n as [|n IH]; intros [|m].
  - execute_arithmetic IH.
  - execute_arithmetic IH.
  - rewrite Nat.sub_0_r. execute_arithmetic IH.
  - execute_arithmetic IH.
Qed.

Corollary add_value_correct n m :
  NatArithmetic.app2 NatArithmetic.add_value (vnat n) (vnat m)
    →* ret (vnat (n + m)).
Proof. apply arithmetic_run_steps, add_value_run. Qed.

Corollary sub_value_correct n m :
  NatArithmetic.app2 NatArithmetic.sub_value (vnat n) (vnat m)
    →* ret (vnat (n - m)).
Proof. apply arithmetic_run_steps, sub_value_run. Qed.

Corollary add_value_terminates n m :
  must_terminating
    (NatArithmetic.app2 NatArithmetic.add_value (vnat n) (vnat m)).
Proof. eapply arithmetic_run_terminates, add_value_run. Qed.

Corollary sub_value_terminates n m :
  must_terminating
    (NatArithmetic.app2 NatArithmetic.sub_value (vnat n) (vnat m)).
Proof. eapply arithmetic_run_terminates, sub_value_run. Qed.

Corollary add_value_result_iff n m v :
  NatArithmetic.app2 NatArithmetic.add_value (vnat n) (vnat m) →* ret v
    <-> v = vnat (n + m).
Proof.
  split; [apply arithmetic_run_unique, add_value_run | intros ->; apply add_value_correct].
Qed.

Corollary sub_value_result_iff n m v :
  NatArithmetic.app2 NatArithmetic.sub_value (vnat n) (vnat m) →* ret v
    <-> v = vnat (n - m).
Proof.
  split; [apply arithmetic_run_unique, sub_value_run | intros ->; apply sub_value_correct].
Qed.
