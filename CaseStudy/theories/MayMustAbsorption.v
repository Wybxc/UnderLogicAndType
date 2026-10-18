(** The additive result with an under branch retains that branch's coverage.
    This is a derived semantic subtyping fact, not a typing constructor. *)
From CaseStudy Require Import MayMustRevised MayMustBase MayMustPrimitives MayMustTyping MayMustUnder.
From ContextTyping Require Import Typing TypingRegular Subtyping BasicBindings SoundnessLam PrimOpConcreteContext.
From Denotation Require Import Context TypeDenoteRegular TypeEquivCore TypeEquiv TypeEquivBody.
From Denotation Require Import BaseIntro TypePersistBase TypeEquivFiberBaseCore
  ResultFirstOpen ResultQualifier.
From ContextLogic Require Import FormulaFiberwise.

Lemma mm_closed_type_lvars τ : basic_context_ty ∅ τ -> context_ty_lvars τ = ∅.
Proof.
  intros Hτ. pose proof (basic_context_ty_to_lvars ∅ τ Hτ) as [H _].
  rewrite lvars_of_atoms_empty in H. set_solver.
Qed.

Lemma mm_under_body_empty P y :
  under_open_body TInt (int_pred P) y =
    FFibVars ∅ (FUnder (FAtom (qual_open_atom 0 y (typed_result_qual TInt (int_pred P))))).
Proof.
  unfold under_open_body,int_pred.
  rewrite param_result_qual_open_vars by set_solver.
  rewrite lvars_of_atoms_empty. f_equal. set_solver.
Qed.

Lemma mm_sum_under_absorb Γ P :
  wf_ctx_under ∅ Γ ->
  sub_type_under ∅ Γ (CTSum (CTOver TInt qual_top) (UInt P)) (UInt P).
Proof.
  intros HΓ.
  set (A := CTOver TInt qual_top).
  assert (HA : basic_context_ty ∅ A) by (apply qual_top_lvars_wf_at; lia).
  assert (Herase : erase_ty A = TBase TInt) by reflexivity.
  assert (Hsum : basic_context_ty ∅ (CTSum A (UInt P))).
  { split; [exact HA|]. split; [apply int_pred_wf|exact Herase]. }
  apply sub_type_under_intro; [exact HΓ| |apply int_pred_wf|exact Herase|].
  { eapply wf_context_ty_at_mono_env with (D:=∅); [apply empty_subseteq|exact Hsum]. }
  intros e m He Hctx Hsource.
  set (Σ := atom_env_to_lty_env (erase_ctx Γ)).
  assert (Hwf : context_typing_wf ∅ Γ e (UInt P)).
  { split; [exact HΓ|]. split; [apply int_pred_wf|exact He]. }
  assert (Hzero : m ⊨ ty_denote_gas 0 Σ (UInt P) e).
  { apply ty_denote_gas_zero_of_guard,ty_guard_relevant_of_static_full_total.
    - exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx).
    - exact (ty_denote_under_total _ _ _ _ _ Hsource). }
  assert (Hsrc : m ⊨ ty_denote_gas 2 Σ (CTSum A (UInt P)) e).
  { exact Hsource. }
  assert (Hsrc0 : m ⊨ ty_denote_gas 0 Σ (CTSum A (UInt P)) e).
  { apply ty_denote_gas_zero_of_guard. exact (ty_denote_gas_guard _ _ _ _ _ Hsrc). }
  pose proof (ty_denote_gas_zero_lc_relevant_env _ _ _ _ Hsrc0) as HlcD.
  set (D := relevant_env Σ (CTSum A (UInt P)) e).
  assert (HD : dom D = dom (relevant_env Σ (UInt P) e)).
  { unfold D. rewrite (ty_denote_gas_zero_relevant_env_dom_eq _ _ _ _ Hsrc0),
      (ty_denote_gas_zero_relevant_env_dom_eq _ _ _ _ Hzero),
      (mm_closed_type_lvars _ Hsum), (mm_closed_type_lvars _ (int_pred_wf 0 ∅ P)).
    reflexivity. }
  unfold ty_denote_under,ty_denote.
  apply (base_refinement_intro false 1 Σ TInt (int_pred P) e m
    (world_dom (m : WorldT) ∪ lvars_fv (dom D) ∪ fv_cty A)); [exact Hzero|].
  intros y my Hy Hiny Hdom Hrest Hres.
  assert (Hym : y ∉ world_dom (m : WorldT)) by (clear -Hy; set_solver).
  assert (HyD : y ∉ lvars_fv (dom D)) by (clear -Hy; set_solver).
  assert (HyA : y ∉ fv_cty A) by (clear -Hy; set_solver).
  assert (HyP : y ∉ fv_cty (UInt P)) by (rewrite (int_pred_fv false P); set_solver).
  change (m ⊨ FAnd (ty_guard_formula D (CTSum A (UInt P)) e)
    (FForall (FImpl (expr_result_formula_at (lvars_shift_from 0 (dom D)) (tm_shift 0 e) (LVBound 0))
      (FPlus (ty_denote_gas 1 (typed_lty_env_bind D (erase_ty A)) (cty_shift 0 A) (tret (vbvar 0)))
        (ty_denote_gas 1 (typed_lty_env_bind D (erase_ty A)) (cty_shift 0 (UInt P)) (tret (vbvar 0))))))) in Hsrc.
  apply res_models_and_iff in Hsrc as [_ Hforall].
  assert (Hlc : lc_tm e) by exact (context_typing_wf_lc_tm _ _ _ _ Hwf).
  assert (Hyef : y ∉ fv_tm e).
  { intros Hin. apply HyD. rewrite <- tm_lvars_fv in Hin.
    exact (lvars_fv_mono _ _ (ty_denote_gas_zero_tm_lvars_dom _ _ _ _ Hsrc0) _ Hin). }
  assert (Hante : my ⊨ formula_open 0 y
    (expr_result_formula_at (lvars_shift_from 0 (dom D)) (tm_shift 0 e) (LVBound 0))).
  { rewrite (formula_open_result_first_expr_result_formula_at_shift0 y (dom D) e HlcD HyD Hlc Hyef).
    rewrite HD. exact Hres. }
  pose proof (result_first_forall_impl_open_elim m my y _ _
    Hforall Hym Hdom Hrest Hante) as Hopened.
  rewrite formula_open_plus in Hopened.
  rewrite !TypeEquivBody.formula_open_shifted_ret_bound0_ty_denote_gas in Hopened
    by (first [rewrite typed_lty_env_bind_lvars_fv_dom; exact HyD|exact HyA|exact HyP]).
  rewrite (cty_open_shift_from_lc_fresh 0 y A (basic_context_ty_lc _ _ HA) HyA),
    (cty_open_shift_from_lc_fresh 0 y (UInt P)
      (basic_context_ty_lc _ _ (int_pred_wf 0 ∅ P)) HyP) in Hopened.
  rewrite (typed_lty_env_bind_open_current y D (erase_ty A)) in Hopened
    by (first [intros Hin; apply HyD,lvars_fv_elem; exact Hin|exact HlcD]).
  apply res_models_plus_iff in Hopened as [ml [mr [Hdef [Hle [_ Hright]]]]].
  pose proof (ty_denote_gas_under_ret_fvar_self_body 0
    (<[LVFree y:=erase_ty A]>D) TInt (int_pred P) y mr
    ltac:(apply lty_env_closed_insert_free; exact HlcD)
    ltac:(rewrite int_pred_dom; set_solver) Hright) as Hbody.
  cbn [polarity_open_body]. rewrite mm_under_body_empty in Hbody |- *.
  apply res_models_fibvars_empty_intro.
  apply res_models_fibvars_empty_elim in Hbody.
  apply (res_models_kripke (res_sum ml mr Hdef) my _ Hle).
  eapply subset_upward_closed_under; [apply FormulaFiberwise.res_subset_sum_r|exact Hbody].
Qed.
