(** Declarative typing of revised Figure 6. *)
From CaseStudy Require Import MayMustRevised MayMustBase MayMustPrimitives MayMustBoolCases.
From ContextTyping Require Import Typing TypingRegular Subtyping BasicBindings
  PrimOpConcreteContext NatCases ConstCases SoundnessLam Weakening.
From Denotation Require Import Context TypeEquiv TypeEquivCore TypeDenoteRegular TypeEquivBody.
From ContextLogic Require Import FormulaConnectives FormulaConnectivesHigher.
From Stdlib Require Import ZArith.

Definition mm_result_pair (l r : Z) : context_ty :=
  CTSum (OInt (fun z => z = l)) (OInt (fun z => z = r)).

Lemma mm_result_pair_wf d D l r : wf_context_ty_at d D (mm_result_pair l r).
Proof. split; [apply int_pred_over_wf|]. split; [apply int_pred_over_wf|reflexivity]. Qed.

Lemma mm_wf_comma_bind Γ x τ :
  wf_ctx_under ∅ Γ -> x ∉ ctx_dom Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ ->
  wf_ctx_under ∅ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros HΓ Hx Hτ.
  pose proof (basic_ctx_erase_dom (dom (∅ : gmap atom ty)) Γ HΓ) as HD.
  split; [exact HΓ|]. split.
  - split; [clear -Hx; set_solver|].
    eapply wf_context_ty_at_mono_env; [|exact Hτ]. rewrite HD. set_solver.
  - cbn [ctx_dom]. clear -Hx. set_solver.
Qed.

Lemma mm_bool_match_pair_typed Φ b :
  has_context_type Φ ∅ (mm_bool_cases b)
    (tmatch (vfvar b) (tret (vint 5)) (tret (vint 2))) (mm_result_pair 5 2).
Proof.
  apply CT_MatchBoth.
  - split; [apply mm_bool_cases_wf|]. split; [apply mm_result_pair_wf|].
    apply TT_Match; [apply VT_FVar,map_lookup_singleton|
      apply TT_Ret,VT_Const|apply TT_Ret,VT_Const].
  - apply CT_Var. split; [split; [set_solver|apply const_precise_wf]|].
    split; [apply const_precise_wf|apply TT_Ret,VT_FVar,map_lookup_singleton].
  - apply CT_Var. split; [split; [set_solver|apply const_precise_wf]|].
    split; [apply const_precise_wf|apply TT_Ret,VT_FVar,map_lookup_singleton].
  - apply typing_int_const. split; [set_solver|apply const_precise_wf].
  - apply typing_int_const. split; [set_solver|apply const_precise_wf].
Qed.

Definition mm_compare_tail (a : atom) : tm :=
  tlete (tprim (op_int_gt 3) (vfvar a))
    (tmatch (vbvar 0) (tret (vint 5)) (tret (vint 2))).

Lemma mm_compare_tail_basic (Δ : gmap atom ty) a :
  Δ !! a = Some (TBase TInt) -> tm_has_type Δ (mm_compare_tail a) (TBase TInt).
Proof.
  intros Ha. unfold mm_compare_tail.
  apply TT_Let with (T1:=TBase TBool) (L:=∅).
  - eapply TT_Op; [reflexivity|]. apply VT_FVar. exact Ha.
  - intros b _. change (tm_has_type (<[b:=TBase TBool]>Δ)
      (tmatch (vfvar b) (tret (vint 5)) (tret (vint 2))) (TBase TInt)).
    apply TT_Match; [apply VT_FVar,map_lookup_insert|
      apply TT_Ret,VT_Const|apply TT_Ret,VT_Const].
Qed.

Lemma mm_compare_tail_typed Γ a :
  wf_ctx_under ∅ (CtxComma Γ (CtxBind a (UInt (fun z => (0 < z)%Z)))) ->
  has_context_type concrete_Φ ∅ (CtxComma Γ (CtxBind a (UInt (fun z => (0 < z)%Z))))
    (mm_compare_tail a) (mm_result_pair 5 2).
Proof.
  intros HΓ. set (Γa := CtxComma Γ (CtxBind a (UInt (fun z => (0 < z)%Z)))).
  assert (Ha : erase_ctx Γa !! a = Some (TBase TInt)).
  { exact (erase_ctx_comma_lookup_new_wf ∅ Γ a _ HΓ). }
  unfold mm_compare_tail.
  apply CT_Let with (τ1:=mm_gt_ty 3 a) (L:=ctx_dom Γa ∪ {[a]}).
  - split; [exact HΓ|]. split; [apply mm_result_pair_wf|apply mm_compare_tail_basic; exact Ha].
  - exact (mm_prim_over_typed Γa (op_int_gt 3) a TInt TBool eq_refl HΓ Ha).
  - intros b Hb.
    assert (Hba : b <> a) by (clear -Hb; set_solver).
    assert (Hnew : wf_ctx_under ∅ (mm_positive_compare_ctx Γ a b 3)).
    { apply mm_wf_comma_bind; [exact HΓ|clear -Hb; set_solver|].
      exact (proj1 (mm_prim_graph_wf Γa (op_int_gt 3) a TInt TBool eq_refl Ha)). }
    change (has_context_type concrete_Φ ∅ (mm_positive_compare_ctx Γ a b 3)
      (tmatch (vfvar b) (tret (vint 5)) (tret (vint 2))) (mm_result_pair 5 2)).
    eapply CT_CtxSub with (Γ2:=mm_bool_cases b).
    + split; [exact Hnew|]. split; [apply mm_result_pair_wf|].
      apply TT_Match; [apply VT_FVar|apply TT_Ret,VT_Const|apply TT_Ret,VT_Const].
      exact (erase_ctx_comma_lookup_new_wf ∅ Γa b _ Hnew).
    + apply mm_bool_match_pair_typed.
    + apply mm_ctx_sub_bool_cases; [exact Hnew| | |].
      * exact (erase_ctx_comma_lookup_new_wf ∅ Γa b _ Hnew).
      * cbn [fv_tm fv_value].
        pose proof (basic_context_ty_fv_subset ∅ _ (mm_result_pair_wf 0 ∅ 5 2)).
        set_solver.
      * intros m Hctx. apply (mm_positive_compare_covers Γ a b 3 m);
          [congruence|lia|exact Hctx].
Qed.

Lemma mm_plus_swap (m : WfWorldT) A B :
  m ⊨ FPlus A B -> m ⊨ FPlus B A.
Proof.
  intros H. apply res_models_plus_iff in H as [ml [mr [Hdef [Hle [Hl Hr]]]]].
  destruct (res_sum_comm_eq ml mr Hdef) as [Hdef' Heq].
  eapply res_models_plus_intro with (Hdef:=Hdef'); [|exact Hr|exact Hl].
  rewrite <- Heq. exact Hle.
Qed.

Lemma mm_forall_impl_plus_swap (m : WfWorldT) A B C :
  formula_scoped_in_world m (FForall (FImpl A (FPlus C B))) ->
  m ⊨ FForall (FImpl A (FPlus B C)) ->
  m ⊨ FForall (FImpl A (FPlus C B)).
Proof.
  intros Hscope Hsource.
  eapply res_models_forall_full_world_map; [exact Hscope| |exact Hsource].
  exists ∅. intros y _ my Hdom Hrest Hbody.
  assert (Hscope' : formula_scoped_in_world my
    (formula_open 0 y (FImpl A (FPlus C B)))).
  { eapply formula_scoped_forall_open_res_le; [exact Hscope| |rewrite Hdom; set_solver].
    apply res_le_of_projection_eq. exact Hrest. }
  rewrite formula_open_impl,formula_open_plus in Hbody,Hscope' |- *.
  apply res_models_impl_intro; [exact Hscope'|]. intros Ha.
  apply mm_plus_swap. exact (res_models_impl_elim my _ _ Hbody Ha).
Qed.

Lemma mm_result_pair_swap Γ l r :
  wf_ctx_under ∅ Γ ->
  sub_type_under ∅ Γ (mm_result_pair l r) (mm_result_pair r l).
Proof.
  intros HΓ. apply sub_type_under_intro;
    [exact HΓ|apply mm_result_pair_wf|apply mm_result_pair_wf|reflexivity|].
  intros e m He Hctx Hsource.
  assert (Hwf : context_typing_wf ∅ Γ e (mm_result_pair r l)).
  { split; [exact HΓ|]. split; [apply mm_result_pair_wf|exact He]. }
  pose proof (ty_denote_under_total ∅ Γ _ e m Hsource) as Htotal.
  pose proof (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx) as Hstatic.
  assert (Hzero : m ⊨ ty_denote_gas 0 (atom_env_to_lty_env (erase_ctx Γ))
    (mm_result_pair r l) e).
  { apply ty_denote_gas_zero_of_guard.
    apply ty_guard_relevant_of_static_full_total; assumption. }
  pose proof (ty_denote_gas_scope_from_zero_any 2 _ _ _ m Hzero) as Hscope.
  pose proof (formula_scoped_and_r _ _ _ Hscope) as Hscope_body.
  unfold ty_denote_under,ty_denote in Hsource |- *.
  cbn [mm_result_pair cty_depth ty_denote_gas] in Hsource |- *.
  apply res_models_and_iff in Hsource as [_ Hbody].
  apply res_models_and_iff. split.
  - apply ty_guard_relevant_of_static_full_total; assumption.
  - apply mm_forall_impl_plus_swap; [exact Hscope_body|exact Hbody].
Qed.

Lemma mm_closed_type_fv τ : basic_context_ty ∅ τ -> fv_cty τ = ∅.
Proof. intros H. pose proof (basic_context_ty_fv_subset ∅ τ H). set_solver. Qed.

Lemma mm_closed_type_open τ x : basic_context_ty ∅ τ -> cty_open 0 x τ = τ.
Proof.
  intros Hτ. apply (cty_open_above_lc_fresh 0 0 x τ); [lia| |].
  - exact (basic_context_ty_lc ∅ τ Hτ).
  - rewrite (mm_closed_type_fv τ Hτ). set_solver.
Qed.

Definition mm_b_ctx g x : ctx :=
  CtxComma (CtxBind g must_help_may_g_ty) (CtxBind x (UInt (fun _ => True))).

Lemma mm_b_ctx_wf g x : g <> x -> wf_ctx_under ∅ (mm_b_ctx g x).
Proof.
  intros Hgx. apply mm_wf_comma_bind.
  - split; [set_solver|apply must_help_may_g_wf].
  - cbn [ctx_dom]. clear -Hgx. set_solver.
  - apply int_pred_wf.
Qed.

Lemma mm_b_ctx_lookups g x : g <> x ->
  erase_ctx (mm_b_ctx g x) !! g = Some (TArrow TInt TInt) /\
  erase_ctx (mm_b_ctx g x) !! x = Some (TBase TInt).
Proof.
  intros Hgx. split.
  - apply erase_ctx_comma_lookup_old,map_lookup_singleton.
  - exact (erase_ctx_comma_lookup_new_wf ∅ _ x _ (mm_b_ctx_wf g x Hgx)).
Qed.

Lemma mm_b_call_typed g x : g <> x ->
  has_context_type concrete_Φ ∅ (mm_b_ctx g x) (tapp (vfvar g) (vfvar x))
    (UInt (fun z => (0 < z)%Z)).
Proof.
  intros Hgx. pose proof (mm_b_ctx_wf g x Hgx) as HΓ.
  destruct (mm_b_ctx_lookups g x Hgx) as [Hg Hx].
  replace (UInt (fun z => (0 < z)%Z)) with
    (cty_open 0 x (UInt (fun z => (0 < z)%Z))) by
    (apply mm_closed_type_open; apply int_pred_wf).
  apply CT_AppFun with (τx:=UInt (fun _ => True)).
  - split; [exact HΓ|]. split.
    + rewrite mm_closed_type_open by apply int_pred_wf. apply int_pred_wf.
    + rewrite cty_open_preserves_erasure. eapply TT_App; apply VT_FVar; eassumption.
  - rewrite (mm_closed_type_fv _ (int_pred_wf 0 ∅ (fun _ => True))),
      (mm_closed_type_fv _ (int_pred_wf 0 ∅ (fun z => (0 < z)%Z))).
    cbn [fv_value]. clear -Hgx. set_solver.
  - apply typing_inter_r with
      (τ1:=CTArrow (OInt (fun _ => True)) (OInt (fun z => (0 < z)%Z))).
    apply typing_comma_prefix_wf; [exact HΓ|].
    apply CT_Var. split; [split; [set_solver|apply must_help_may_g_wf]|].
    split; [apply must_help_may_g_wf|apply TT_Ret,VT_FVar,map_lookup_singleton].
  - apply typing_var_right_wf. exact HΓ.
Qed.

Definition mm_b_body g x : tm :=
  tlete (tapp (vfvar g) (vfvar x))
    (tlete (tprim (op_int_gt 3) (vbvar 0))
      (tmatch (vbvar 0) (tret (vint 5)) (tret (vint 2)))).

Lemma mm_b_body_basic Δ g x :
  Δ !! g = Some (TArrow TInt TInt) -> Δ !! x = Some (TBase TInt) ->
  tm_has_type Δ (mm_b_body g x) (TBase TInt).
Proof.
  intros Hg Hx. unfold mm_b_body.
  apply TT_Let with (T1:=TBase TInt) (L:=∅).
  - eapply TT_App; apply VT_FVar; eassumption.
  - intros a _. change (tm_has_type (<[a:=TBase TInt]>Δ) (mm_compare_tail a) (TBase TInt)).
    apply mm_compare_tail_basic,map_lookup_insert.
Qed.

Lemma mm_b_body_typed g x : g <> x ->
  has_context_type concrete_Φ ∅ (mm_b_ctx g x) (mm_b_body g x) (mm_result_pair 2 5).
Proof.
  intros Hgx. pose proof (mm_b_ctx_wf g x Hgx) as HΓ.
  destruct (mm_b_ctx_lookups g x Hgx) as [Hg Hx].
  eapply CT_Sub with (τ1:=mm_result_pair 5 2).
  - split; [exact HΓ|]. split; [apply mm_result_pair_wf|apply mm_b_body_basic; assumption].
  - unfold mm_b_body. apply CT_Let with (τ1:=UInt (fun z => (0 < z)%Z))
      (L:=ctx_dom (mm_b_ctx g x)).
    + split; [exact HΓ|]. split; [apply mm_result_pair_wf|apply mm_b_body_basic; assumption].
    + apply mm_b_call_typed. exact Hgx.
    + intros a Ha. change (has_context_type concrete_Φ ∅
        (CtxComma (mm_b_ctx g x) (CtxBind a (UInt (fun z => (0 < z)%Z))))
        (mm_compare_tail a) (mm_result_pair 5 2)).
      apply mm_compare_tail_typed. apply mm_wf_comma_bind; [exact HΓ|exact Ha|apply int_pred_wf].
  - apply mm_result_pair_swap. exact HΓ.
Qed.

Theorem must_help_may_context_typed g :
  has_context_type concrete_Φ ∅ (CtxBind g must_help_may_g_ty)
    (tret (must_help_may g)) must_help_may_ty.
Proof.
  unfold must_help_may_ty,must_help_may.
  apply CT_Lam with (τx:=UInt (fun _ => True)) (L:={[g]}).
  - split; [split; [set_solver|apply must_help_may_g_wf]|].
    split; [apply must_help_may_wf|].
    apply TT_Ret,must_help_may_basic,map_lookup_singleton.
  - intros x Hx. apply not_elem_of_singleton in Hx.
    rewrite mm_closed_type_open by apply mm_result_pair_wf.
    change (has_context_type concrete_Φ ∅ (mm_b_ctx g x) (mm_b_body g x) (mm_result_pair 2 5)).
    apply mm_b_body_typed. congruence.
Qed.

From ContextTyping Require Import Soundness.
Corollary must_help_may_context_sound g :
  ctx_denote_under ∅ (CtxBind g must_help_may_g_ty) ⊫
    ty_denote_under ∅ (CtxBind g must_help_may_g_ty)
      must_help_may_ty (tret (must_help_may g)).
Proof. apply concrete_Fundamental,must_help_may_context_typed. Qed.

Print Assumptions must_help_may_context_typed.
Print Assumptions must_help_may_context_sound.
