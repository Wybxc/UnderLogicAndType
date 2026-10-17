(** Administrative reduction of the actual generator, preserving both
    results and must termination. *)
From CaseStudy Require Import CaseTypes BSTGeneratorProgram
  NatArithmeticUnfolding ArithmeticProofTools.
From CoreLang Require Import BasicTyping SmallStep Sugar.
From ContextBasicDenotation Require Import TermSyntax.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From CaseStudy Require Import NatArithmeticStages.

Lemma bst_gen_value_basic_typed : value_has_type ∅ bst_gen_value bst_gen_basic_ty.
Proof.
  pose proof bst_gen_basic_typed as H.
  change (tm_has_type ∅ (tret bst_gen_value) bst_gen_basic_ty) in H.
  inversion H; subst. assumption.
Qed.

Lemma bst_call_variables_fv u v g :
  fv_tm (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g)) = {[u;v;g]}.
Proof.
  assert (HG : fv_value bst_gen_value = ∅).
  { eapply basic_typing_closed_value. exact bst_gen_value_basic_typed. }
  unfold NatArithmetic.app3,NatArithmetic.app2. rewrite !fv_tapp_tm.
  change ((fv_value bst_gen_value ∪ {[u]}) ∪ {[v]} ∪ {[g]} = {[u;v;g]}).
  rewrite HG. set_solver.
Qed.

Lemma bst_call_instantiate σ n lo x g :
  σ !! x = Some g -> lc_value g ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (NatArithmetic.app3 bst_gen_value (vnat n) (vnat lo) (vfvar x)) =
  NatArithmetic.app3 bst_gen_value (vnat n) (vnat lo) g.
Proof.
  intros Hx Hg.
  change (lstore_instantiate_tm (lstore_lift_free σ)
    (NatArithmetic.app3 bst_gen_value (vnat n) (vnat lo) (vfvar x)) =
    tlete (NatArithmetic.app2 bst_gen_value (vnat n) (vnat lo))
      (tapp (vbvar 0) (value_shift 0 g))).
  rewrite value_shift_lc_id by exact Hg.
  arithmetic_instantiate. setoid_rewrite Hx. vm_compute. reflexivity.
Qed.

Lemma bst_call_basic_typed Δ n lo g :
  value_has_type Δ g (TNat →ᵦ TNat →ᵦ TNat) ->
  tm_has_type Δ (NatArithmetic.app3 bst_gen_value (vnat n) (vnat lo) g)
    (TBase TTree).
Proof.
  intros Hg. unfold NatArithmetic.app3, NatArithmetic.app2.
  eapply basic_typing_tapp_tm; [|exact Hg].
  eapply basic_typing_tapp_tm; [|constructor].
  eapply TT_App; [|constructor].
  eapply (basic_typing_weaken_value ∅ Δ);
    [exact bst_gen_value_basic_typed|apply map_empty_subseteq].
Qed.

Lemma bst_call_variables_instantiate σ n a u v g vg :
  σ !! u = Some (vnat n) -> σ !! v = Some (vnat a) ->
  σ !! g = Some vg -> lc_value vg ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g)) =
  NatArithmetic.app3 bst_gen_value (vnat n) (vnat a) vg.
Proof.
  intros Hu Hv Hg Hlc.
  change (lstore_instantiate_tm (lstore_lift_free σ)
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g)) =
    tlete (NatArithmetic.app2 bst_gen_value (vnat n) (vnat a))
      (tapp (vbvar 0) (value_shift 0 vg))).
  rewrite value_shift_lc_id by exact Hlc.
  arithmetic_instantiate. setoid_rewrite Hu. setoid_rewrite Hv. setoid_rewrite Hg.
  vm_compute. reflexivity.
Qed.

Lemma bst_call_variables_basic_typed Δ u v g :
  Δ !! u = Some (TBase TNat) -> Δ !! v = Some (TBase TNat) ->
  Δ !! g = Some (TNat →ᵦ TNat →ᵦ TNat) ->
  tm_has_type Δ
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g)) (TBase TTree).
Proof.
  intros Hu Hv Hg. unfold NatArithmetic.app3, NatArithmetic.app2.
  eapply basic_typing_tapp_tm; [|apply VT_FVar; exact Hg].
  eapply basic_typing_tapp_tm; [|apply VT_FVar; exact Hv].
  eapply TT_App; [|apply VT_FVar; exact Hu].
  eapply (basic_typing_weaken_value ∅ Δ);
    [exact bst_gen_value_basic_typed|apply map_empty_subseteq].
Qed.

Local Lemma typed_prefix_step Δ e e' target T :
  tm_has_type Δ e T ->
  (step e e' /\ forall z, step e z -> z = e') ->
  (tm_has_type Δ e' T -> arithmetic_prefix e' target) ->
  arithmetic_prefix e target.
Proof.
  intros Hty Hstep Hnext. eapply Prefix_step; [exact Hstep|].
  apply Hnext. eapply step_preserves_type; [exact Hty|exact (proj1 Hstep)].
Qed.

Local Ltac bst_head Hlc :=
  first [apply HS_Ret | apply HS_Beta | apply HS_Fix |
    apply HS_MatchTrue | apply HS_MatchFalse |
    (apply HS_Op; [constructor|])]; exact Hlc.

Local Ltac bst_certify_step Hlc :=
  lazymatch goal with
  | |- step (tlete (tret _) _) _ /\ _ =>
      split; [apply Step_head; bst_head Hlc|
        eapply arithmetic_head_deterministic;
        [bst_head Hlc|intros op c H; discriminate]]
  | |- step (tlete ?e1 ?e2) _ /\ _ =>
      let Hlc1 := fresh "Hlc1" in
      pose proof (proj1 (proj1 (lc_lete_iff_body e1 e2) Hlc)) as Hlc1;
      apply arithmetic_certified_let; [bst_certify_step Hlc1|exact Hlc]
  | |- step _ _ /\ _ =>
      split; [apply Step_head; bst_head Hlc|
        eapply arithmetic_head_deterministic;
        [bst_head Hlc|intros op c H; inversion H; subst; split; discriminate]]
  end.

Local Ltac bst_prefix_steps Δ T Hty :=
  first [apply Prefix_refl|
    lazymatch goal with |- arithmetic_prefix ?e ?target =>
      let e' := eval vm_compute in e in
      change (arithmetic_prefix e' target);
      eapply (typed_prefix_step Δ e' _ target T Hty);
      [let Hlc := fresh "Hlc" in
        pose proof (typing_tm_lc Δ e' T Hty) as Hlc;
        bst_certify_step Hlc|
        let Hnext := fresh "Hnext" in intros Hnext; bst_prefix_steps Δ T Hnext]
    end].

Lemma bst_zero_call_prefix Δ lo g :
  value_has_type Δ g (TNat →ᵦ TNat →ᵦ TNat) ->
  arithmetic_prefix (NatArithmetic.app3 bst_gen_value (vnat 0) (vnat lo) g)
    (tret (vconst (ctree tr_leaf))).
Proof.
  intros Hg. pose proof (bst_call_basic_typed Δ 0 lo g Hg) as Hty.
  bst_prefix_steps Δ (TBase TTree) Hty.
Qed.

(** These are administrative views of the original closed value.  They do
    not replace its body or evaluate either recursive call. *)
Definition bst_partial (vr : value) : value :=
  match bst_gen_value with
  | vfix _ (vlam _ (tret v)) =>
      open_value 0 bst_gen_value (open_value 1 vr v)
  | _ => vconst cunit
  end.

Definition bst_lower_partial (vr vlo : value) : value :=
  match bst_partial vr with
  | vlam _ (tret v) => open_value 0 vlo v
  | _ => vconst cunit
  end.

Definition bst_open_body (vr vlo vg : value) : tm :=
  match bst_lower_partial vr vlo with
  | vlam _ body => open_tm 0 vg body
  | _ => tret (vconst cunit)
  end.

Definition bst_positive_branch (vr vlo vg : value) : tm :=
  match bst_open_body vr vlo vg with
  | tlete _ (tmatch _ _ ef) => open_tm 0 (vconst (cbool false)) ef
  | _ => tret (vconst cunit)
  end.

Definition bst_range_lam_body vr vlo : tm :=
  match bst_lower_partial vr vlo with
  | vlam _ body => body
  | _ => tret (vconst cunit)
  end.

Lemma bst_lower_partial_lam vr vlo :
  bst_lower_partial vr vlo = vlam BSTProgram.range_basic_ty (bst_range_lam_body vr vlo).
Proof. reflexivity. Qed.

Local Lemma bst_prefix_trans e e' e'' :
  arithmetic_prefix e e' -> arithmetic_prefix e' e'' -> arithmetic_prefix e e''.
Proof. intros H. induction H; intros Hnext; [exact Hnext|eapply Prefix_step; eauto]. Qed.

Local Lemma bst_prefix_preserves_type Δ e e' T :
  arithmetic_prefix e e' -> tm_has_type Δ e T -> tm_has_type Δ e' T.
Proof.
  intros H. induction H as [e|e e' e'' [Hs Hd] Hpref IH]; intros Hty;
    [exact Hty|apply IH; eapply step_preserves_type; eauto].
Qed.

Local Lemma bst_prefix_under_let Δ e e' body T :
  arithmetic_prefix e e' -> tm_has_type Δ (tlete e body) T ->
  arithmetic_prefix (tlete e body) (tlete e' body).
Proof.
  intros H. induction H as [e|e e' e'' Hstep Hpref IH]; intros Hty.
  - apply Prefix_refl.
  - eapply typed_prefix_step; [exact Hty| |exact IH].
    apply arithmetic_certified_let; [exact Hstep|].
    exact (typing_tm_lc _ _ _ Hty).
Qed.

Lemma bst_lower_partial_prefix n a :
  arithmetic_prefix (NatArithmetic.app2 bst_gen_value (vnat n) (vnat a))
    (tret (bst_lower_partial (vnat n) (vnat a))).
Proof.
  assert (Hty : tm_has_type ∅ (NatArithmetic.app2 bst_gen_value (vnat n) (vnat a))
    (BSTProgram.range_basic_ty →ᵦ TTree)).
  { unfold NatArithmetic.app2. eapply basic_typing_tapp_tm; [|constructor].
    eapply TT_App; [|constructor]. eapply basic_typing_weaken_value;
      [exact bst_gen_value_basic_typed|apply map_empty_subseteq]. }
  bst_prefix_steps (∅ : gmap atom ty) (BSTProgram.range_basic_ty →ᵦ TTree) Hty.
Qed.

Lemma bst_call_body_prefix Δ n a g :
  value_has_type Δ g (TNat →ᵦ TNat →ᵦ TNat) ->
  arithmetic_prefix (NatArithmetic.app3 bst_gen_value (vnat n) (vnat a) g)
    (bst_open_body (vnat n) (vnat a) g).
Proof.
  intros Hg. pose proof (bst_call_basic_typed Δ n a g Hg) as Hty.
  pose proof (typing_value_lc _ _ _ Hg) as Hglc.
  unfold NatArithmetic.app3, tapp_tm in Hty |- *.
  eapply bst_prefix_trans with (e':=tlete
    (tret (bst_lower_partial (vnat n) (vnat a)))
    (tapp (vbvar 0) (value_shift 0 g))).
  - eapply (bst_prefix_under_let Δ _ _ _ (TBase TTree)); [exact (bst_lower_partial_prefix n a)|exact Hty].
  - assert (Hty' : tm_has_type Δ
      (tlete (tret (bst_lower_partial (vnat n) (vnat a)))
        (tapp (vbvar 0) (value_shift 0 g))) (TBase TTree)).
    { eapply bst_prefix_preserves_type; [|exact Hty].
      eapply (bst_prefix_under_let Δ _ _ _ (TBase TTree)); [exact (bst_lower_partial_prefix n a)|exact Hty]. }
    rewrite value_shift_lc_id in Hty' |- * by exact Hglc.
    set (F := bst_lower_partial (vnat n) (vnat a)).
    assert (Hopen : open_tm 0 F (tapp (vbvar 0) g) = tapp F g).
    { change (tapp F (open_value 0 F g) = tapp F g).
      rewrite open_rec_lc_value by exact Hglc. reflexivity. }
    assert (Hhead : head_step (tlete (tret F) (tapp (vbvar 0) g)) (tapp F g)).
    { rewrite <- Hopen. apply HS_Ret. exact (typing_tm_lc _ _ _ Hty'). }
    eapply (typed_prefix_step Δ _ (tapp F g) _ (TBase TTree) Hty').
    + split; [apply Step_head; exact Hhead|].
      eapply arithmetic_head_deterministic; [exact Hhead|intros op c H; discriminate].
    + intros HtyF. unfold F. rewrite bst_lower_partial_lam.
      unfold bst_open_body. rewrite bst_lower_partial_lam.
      cbn [bst_range_lam_body].
      eapply Prefix_step; [|apply Prefix_refl].
      split; [apply Step_head, HS_Beta; exact (typing_tm_lc _ _ _ HtyF)|].
      eapply arithmetic_head_deterministic;
        [apply HS_Beta; exact (typing_tm_lc _ _ _ HtyF)|intros op c H; discriminate].
Qed.

Lemma bst_positive_call_prefix Δ n a g :
  value_has_type Δ g (TNat →ᵦ TNat →ᵦ TNat) ->
  arithmetic_prefix (NatArithmetic.app3 bst_gen_value (vnat (S n)) (vnat a) g)
    (bst_positive_branch (vnat (S n)) (vnat a) g).
Proof.
  intros Hg. pose proof (bst_call_basic_typed Δ (S n) a g Hg) as Hty.
  pose proof (bst_call_body_prefix Δ (S n) a g Hg) as Hpref.
  eapply bst_prefix_trans; [exact Hpref|].
  pose proof (bst_prefix_preserves_type Δ _ _ _ Hpref Hty) as Hbody.
  bst_prefix_steps Δ (TBase TTree) Hbody.
Qed.

Lemma bst_partial_prefix n :
  arithmetic_prefix (tapp_tm (tret bst_gen_value) (vnat n))
    (tret (bst_partial (vnat n))).
Proof.
  assert (Hty : tm_has_type ∅ (tapp_tm (tret bst_gen_value) (vnat n))
    BSTProgram.result_fun_ty).
  { eapply basic_typing_tapp_tm; [apply TT_Ret; exact bst_gen_value_basic_typed|constructor]. }
  bst_prefix_steps (∅ : gmap atom ty) BSTProgram.result_fun_ty Hty.
Qed.

Definition bst_partial_lam_body vr : tm :=
  match bst_partial vr with vlam _ body => body | _ => tret (vconst cunit) end.

Lemma bst_partial_lam vr :
  bst_partial vr = vlam TNat (bst_partial_lam_body vr).
Proof. reflexivity. Qed.

Lemma bst_partial_lower_open u v :
  open_tm 0 (vfvar v) (bst_partial_lam_body (vfvar u)) =
    tret (bst_lower_partial (vfvar u) (vfvar v)).
Proof. reflexivity. Qed.

Lemma bst_partial_variable_basic Δ u :
  Δ !! u = Some (TBase TNat) ->
  value_has_type Δ (bst_partial (vfvar u)) BSTProgram.result_fun_ty.
Proof.
  intros Hu.
  assert (Hty : tm_has_type Δ (tapp_tm (tret bst_gen_value) (vfvar u))
    BSTProgram.result_fun_ty).
  { eapply basic_typing_tapp_tm; [apply TT_Ret|apply VT_FVar; exact Hu].
    eapply basic_typing_weaken_value; [exact bst_gen_value_basic_typed|apply map_empty_subseteq]. }
  assert (Hpref : arithmetic_prefix (tapp_tm (tret bst_gen_value) (vfvar u))
    (tret (bst_partial (vfvar u)))).
  { bst_prefix_steps Δ BSTProgram.result_fun_ty Hty. }
  pose proof (bst_prefix_preserves_type Δ _ _ _ Hpref Hty) as Hret.
  inversion Hret. assumption.
Qed.

Lemma bst_lower_partial_variables_basic Δ u v :
  Δ !! u = Some (TBase TNat) -> Δ !! v = Some (TBase TNat) ->
  value_has_type Δ (bst_lower_partial (vfvar u) (vfvar v))
    (BSTProgram.range_basic_ty →ᵦ TTree).
Proof.
  intros Hu Hv.
  assert (Hty : tm_has_type Δ (NatArithmetic.app2 bst_gen_value (vfvar u) (vfvar v))
    (BSTProgram.range_basic_ty →ᵦ TTree)).
  { unfold NatArithmetic.app2. eapply basic_typing_tapp_tm; [eapply TT_App|apply VT_FVar; exact Hv].
    - eapply basic_typing_weaken_value; [exact bst_gen_value_basic_typed|apply map_empty_subseteq].
    - apply VT_FVar. exact Hu. }
  assert (Hpref : arithmetic_prefix (NatArithmetic.app2 bst_gen_value (vfvar u) (vfvar v))
    (tret (bst_lower_partial (vfvar u) (vfvar v)))).
  { bst_prefix_steps Δ (BSTProgram.range_basic_ty →ᵦ TTree) Hty. }
  pose proof (bst_prefix_preserves_type Δ _ _ _ Hpref Hty) as Hret.
  inversion Hret. assumption.
Qed.

Lemma bst_open_body_variables_basic Δ u v g :
  Δ !! u = Some (TBase TNat) -> Δ !! v = Some (TBase TNat) ->
  Δ !! g = Some BSTProgram.range_basic_ty ->
  tm_has_type Δ (bst_open_body (vfvar u) (vfvar v) (vfvar g)) (TBase TTree).
Proof.
  intros Hu Hv Hg.
  pose proof (bst_call_variables_basic_typed Δ u v g Hu Hv Hg) as Hty.
  assert (Hpref : arithmetic_prefix
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g))
    (bst_open_body (vfvar u) (vfvar v) (vfvar g))).
  { bst_prefix_steps Δ (TBase TTree) Hty. }
  exact (bst_prefix_preserves_type Δ _ _ _ Hpref Hty).
Qed.
