(** * ContextTyping.SoundnessArrowIntro

    Soundness of value eta introduction for over-base arguments. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  DenotationSetMapFacts
  ResultFirstOpen
  TypeEquivCore
  TypeEquivFiberBaseCore TypeEquivFiberBaseProjected
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  TypePersistArrow
  ConstDenote.
From ContextTyping Require Import Typing TypingRegular SoundnessLam
  SoundnessFixBase SoundnessFixApply
  SoundnessFixSelf.

Lemma value_arrow_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ vf
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret vf) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros Hwf Hy Hctx_comma.
  assert (Hwf_app :
      context_typing_wf Σ (CtxComma Γ (CtxBind y τx))
        (tapp_tm (tret vf) (vfvar y))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ Γ
      (tret vf) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret vf) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx Hτ].
    split.
    + unfold wf_ctx_under. cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
      * apply basic_ctx_bind.
        -- rewrite <- HdomΓ.
           eapply context_union_fresh_env_erase_ctx. exact Hy.
        -- eapply (wf_context_ty_at_mono_env
             0 (dom (erase_ctx Γ)) (dom Σ ∪ ctx_dom Γ)).
           ++ rewrite HdomΓ. better_set_solver.
           ++ exact Hτx.
      * cbn [ctx_dom]. rewrite <- HdomΓ.
        apply elem_of_disjoint. intros a Ha Hay.
        apply elem_of_singleton in Hay. subst a.
        eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy. exact Ha.
    + split.
      * eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxComma Γ (CtxBind y τx))))).
        -- rewrite erase_ctx_comma_bind_dom. reflexivity.
        -- apply wf_context_ty_at_open_at.
           ++ eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
           ++ exact Hτ.
      * rewrite cty_open_preserves_erasure.
        replace (erase_ctx (CtxComma Γ (CtxBind y τx)))
          with (<[y := erase_ty τx]> (erase_ctx Γ)).
        -- apply basic_typing_tapp_tm_fvar_insert.
           ++ eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
           ++ exact (context_typing_wf_basic_typing Σ Γ
                (tret vf) (CTArrow τx τ) Hwf).
        -- symmetry. apply erase_ctx_comma_bind_fresh.
           eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
  }
  eapply context_typing_wf_denot_static_guard_comma_bind_insert; eauto.
  eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
Qed.

Lemma value_arrow_open_arg_normalize
    (Σ : tyctx) Γ τx τ vf
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret vf) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret vf))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  assert (Hlcτx : lc_context_ty τx).
  {
    apply (context_typing_wf_arrow_arg_lc Σ Γ
      (tret vf) τx τ).
    exact Hwf.
  }
  rewrite formula_open_ty_denote_gas_bind_ret_bvar0 in Harg.
  2:{ apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    apply relevant_env_arrow_fresh_free.
    - clear -Hy. better_set_solver.
    - clear -Hy. better_set_solver.
    - cbn [fv_tm]. clear -Hy. better_set_solver.
  }
  2:{ clear -Hy. better_set_solver. }
  2:{ exact Hlcτx. }
  exact (arrow_open_arg_to_inserted_env
    (Nat.max (cty_depth τx) (cty_depth τ))
    (atom_env_to_lty_env (erase_ctx Γ)) τx τ
    (tret vf) my y Harg).
Qed.

Lemma value_arrow_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ vf
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret vf) (CTArrow τx τ) ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Harg.
  eapply ty_denote_gas_ret_fvar_insert_ctx_erasure_under.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret vf) (CTArrow τx τ) Hwf) as Hwfctx.
    exact (wf_ctx_under_basic Σ Γ Hwfctx).
  - pose proof (context_typing_wf_context_ty Σ Γ
      (tret vf) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    eapply wf_context_ty_at_fv_subset. exact Hτx.
  - exact Harg.
Qed.

Lemma value_arrow_open_arg_to_bind_ctx
    (Σ : tyctx) Γ τx τ vf
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret vf) (CTArrow τx τ) ->
  my ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
  intros Hwf Hctx_my Hdom Hrestrict Hy Harg.
  pose proof (value_arrow_open_arg_to_bind_denotation
    Σ Γ τx τ vf my y Hwf Harg)
    as Hbind_den.
  eapply ctx_bind_from_inserted_erasure_arg_denotation.
  - eapply context_union_fresh_ctx_erasure_under. exact Hy.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret vf) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret vf) (CTArrow τx τ) Hwf) as Hτwf.
    cbn [wf_context_ty_at] in Hτwf.
    destruct Hτwf as [Hτx _].
    eapply ty_env_agree_ctx_erasure_under_of_basic_ctx.
    + exact HbasicΓ.
    + eapply wf_context_ty_at_fv_subset. exact Hτx.
  - exact Hctx_my.
  - exact Hbind_den.
Qed.

Lemma value_arrow_open_arg_to_comma_ctx
    (Σ : tyctx) Γ τx τ vf
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret vf) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros Hwf Hctx Hdom Hrestrict Hy Harg.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret vf) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  assert (Hctx_my : my ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact Hctx_my|].
  eapply value_arrow_open_arg_to_bind_ctx; eauto.
Qed.

Lemma value_result_first_outer_result_plain
    (Σ : tyctx) Γ φx τ vf b
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret vf)
    (CTArrow (over_ty b φx) τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow (over_ty b φx) τ)
          (tret vf))))
      (tm_shift 0 (tret vf)) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret vf) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow (over_ty b φx) τ)
            (tret vf))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow (over_ty b φx) τ)
            (tret vf))))).
  {
    rewrite lvars_shift_from_fv.
    intros Hzbad.
    apply lvars_fv_elem in Hzbad.
    pose proof (soundness_relevant_env_arrow_value_fresh
      (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
      vf z
      ltac:(cbn; clear -Hz; better_set_solver)) as Hnot.
    exact (Hnot Hzbad).
  }
  assert (Hlc_efix :
      lc_tm (tret vf)).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret vf)
      (CTArrow (over_ty b φx) τ) Hwf).
  }
  assert (Hz_efix :
      z ∉ fv_tm (tret vf)).
  {
    cbn [fv_tm].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_efix || exact Hz_efix).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow (over_ty b φx) τ)
      (tret vf)))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret vf))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow (over_ty b φx) τ)
      (tret vf)))).
  - intros v Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret vf)
        (CTArrow (over_ty b φx) τ) Hwf) as Hfv.
      destruct v as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret vf)
          (CTArrow (over_ty b φx) τ) Hwf) as Hlc.
        exfalso.
        pose proof (tm_lvars_lc _ Hlc (LVBound k) Hv) as [].
      * rewrite atom_store_to_lvar_store_dom.
        apply elem_of_map. exists a. split; [reflexivity|].
        apply Hfv.
        rewrite <- tm_lvars_fv.
        apply (proj2 (lvars_fv_elem _ _)).
        exact Hv.
    + unfold relevant_lvars. set_solver.
  - set_solver.
  - intros Hzbad.
    pose proof (soundness_relevant_env_arrow_value_fresh
      (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
      vf z
      ltac:(cbn; clear -Hz; better_set_solver)) as Hnot.
    exact (Hnot Hzbad).
  - exact Hres.
Qed.

Lemma value_result_first_arrow_value_denotation
    Σ Γ φx τ vf b (L : aset)
    (m mz : WfWorldT) z :
  context_typing_wf Σ Γ (tret vf) (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (cty_open 0 y τ) (tapp_tm (tret vf) (vfvar y))) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (arrow_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      (<[LVFree z := erase_ty (CTArrow (over_ty b φx) τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow (over_ty b φx) τ)
          (tret vf)))
      (over_ty b φx) τ
      (tret (vfvar z))) ->
  mz ⊨ expr_result_formula (tret vf) (LVFree z) ->
  mz ⊨ arrow_value_denote_gas_with ty_denote_gas
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    (<[LVFree z := erase_ty (CTArrow (over_ty b φx) τ)]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow (over_ty b φx) τ)
        (tret vf)))
    (over_ty b φx) τ
    (tret (vfvar z)).
Proof.
  intros Hwf IH Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (τx := over_ty b φx).
  set (efix := tret vf).
  set (vself := vf).
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTArrow τx τ) efix).
  change (over_ty b φx) with τx in Hscope_value.
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (context_typing_wf_context_ty
    Σ Γ efix (CTArrow τx τ) ltac:(subst efix τx; exact Hwf))
    as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  eapply res_models_forall_rev_intro; [exact Hscope_value|].
  exists (L ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪ fv_cty τx ∪
    fv_cty τ ∪ {[z]}).
  intros y Hy my Hdomy Hrestricty.
  assert (Hle_mz_my : mz ⊑ my).
  { rewrite <- Hrestricty. apply res_restrict_le. }
  assert (Hy_world : y ∈ world_dom (my : WorldT)).
  { rewrite Hdomy. apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
  cbn [formula_open arrow_value_denote_gas_with] in Hscope_value |- *.
  pose proof (formula_scoped_forall_open_res_le
    mz my y _ Hscope_value Hle_mz_my Hy_world) as Hopened_scope.
  cbn [formula_open] in Hopened_scope |- *.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Harg_raw.
  assert (Hy_fresh :
      y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value vf ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  { clear -Hy. better_set_solver. }
  assert (Hy_rest :
      y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value vf ∪ fv_cty τx ∪ fv_cty τ).
  { clear -Hy_fresh. better_set_solver. }
  assert (Harg_norm :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        τx (tret (vfvar y))).
  {
    change (my ⊨ formula_open 0 y
      (ty_denote_gas gas
        (typed_lty_env_bind
          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))))
      in Harg_raw.
    rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
      y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
      τx) in Harg_raw.
    2:{ apply lty_env_closed_insert_free.
        subst Σrel Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
    2:{
      rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      - apply elem_of_singleton in Hin. inversion Hin. subst.
        clear -Hy_fresh. set_solver.
      - exfalso.
        subst Σrel Δ efix τx.
        pose proof (soundness_relevant_env_arrow_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
          vf y
          ltac:(cbn; clear -Hy_fresh; better_set_solver))
          as Hnot.
        exact (Hnot Hin).
    }
    2:{ clear -Hy_fresh. better_set_solver. }
    2:{ exact Hτx_lc. }
    exact Harg_raw.
  }
  assert (Harg_old :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree y := erase_ty τx]>
        (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - rewrite lty_env_insert_free_commute by (clear -Hy_fresh; set_solver).
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm] in Hzbad;
            clear -Hz Hy_fresh Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTArrow τx τ)) Hz_rel_arg).
      apply lam_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst efix vself τx. cbn.
        clear -Hy_fresh. better_set_solver.
    - exact Harg_norm.
  }
  assert (Hres_my :
      my ⊨ expr_result_formula efix (LVFree z)).
  {
    eapply res_models_kripke; [exact Hle_mz_my|exact Hres_z].
  }
  pose proof (value_arrow_opened_app_static_guard_full
    Σ Γ τx τ vf my y
    ltac:(subst τx; exact Hwf)
    ltac:(clear -Hy_fresh; better_set_solver)) as Hstatic_app_need.
  assert (Harg_depth :
      my ⊨ ty_denote_gas (cty_depth τx)
        (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))).
  {
    rewrite <- (ty_denote_gas_saturate gas
      (<[LVFree y := erase_ty τx]> Δ)
      τx (tret (vfvar y))) by lia.
    exact Harg_old.
  }
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (value_arrow_open_arg_to_comma_ctx Σ Γ τx τ vf mz my y).
    - subst τx. exact Hwf.
    - exact Hctx_mz.
    - exact Hdomy.
    - exact Hrestricty.
    - clear -Hy_fresh. better_set_solver.
    - exact Harg_depth.
  }
  pose proof (Hstatic_app_need Hctx_comma) as Hstatic_app.
  assert (Hfun_basic :
      my ⊨ expr_basic_typing_formula
        (<[LVFree y := erase_ty τx]> Δ)
        efix (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
  {
    apply expr_basic_typing_formula_models_iff.
    split.
    - apply lty_env_closed_insert_free. apply atom_store_to_lvar_store_closed.
    - split.
      + pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_app)
          as Hworld_app.
        apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope _]].
        exact Hscope.
      + rewrite cty_open_preserves_erasure.
        eapply basic_tm_has_ltype_weaken.
        * subst Δ efix τx.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret vf)
            (CTArrow (over_ty b φx) τ) Hwf).
        * apply insert_subseteq. apply not_elem_of_dom.
          apply atom_env_to_lty_env_dom_free_notin.
          eapply (soundness_fresh_erase_ctx_from_context_union
            Σ Γ y (fv_value vf) (fv_cty τx) (fv_cty τ)).
          clear -Hy_fresh. better_set_solver.
  }
  assert (Hlc_vself : lc_value vself).
  {
    subst vself efix.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret vf)
      (CTArrow (over_ty b φx) τ) Hwf).
  }
	  assert (Hz_insert_env :
	      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
	  {
	    subst Δ. apply
	      (ctx_erasure_under_inserted_erase_ctx_lty_env_fresh
	        Σ Γ z y (erase_ty τx)).
	    - clear -Hy_fresh. set_solver.
	    - clear -Hz. better_set_solver.
	  }
	  assert (Hz_alias_fresh :
	      z ∉ fv_value vself ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
	  {
	    apply value_open_result_alias_fresh.
	    subst vself. cbn.
	    clear -Hy_fresh Hz. better_set_solver.
	  }
  assert (Happ_src_mid :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        (cty_open 0 y τ) (tapp_tm efix (vfvar y))).
  {
    pose proof (IH y ltac:(clear -Hy_fresh; better_set_solver) my Hctx_comma) as Hcall.
    unfold ty_denote_under, ty_denote in Hcall.
    rewrite erase_ctx_comma_bind_fresh in Hcall.
    2:{ eapply (context_union_fresh_erase_ctx_from_erasure_under
          Σ Γ y (fv_value vf) (fv_cty τx) (fv_cty τ)).
        clear -Hy_fresh. better_set_solver. }
    change (my ⊨ ty_denote_gas (cty_depth (cty_open 0 y τ))
      (atom_env_to_lty_env (<[y := erase_ty τx]> (erase_ctx Γ)))
      (cty_open 0 y τ) (tapp_tm (tret vf) (vfvar y))) in Hcall.
    assert (Henv : atom_env_to_lty_env (<[y := erase_ty τx]> (erase_ctx Γ)) =
      <[LVFree y := erase_ty τx]> Δ).
    { subst Δ. apply atom_store_to_lvar_store_insert. }
    rewrite <- Henv.
    rewrite ty_denote_gas_saturate by (rewrite cty_open_preserves_depth; lia).
    exact Hcall.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
    vself y z (erase_ty τx) my
    Hz_insert_env Hz_alias_fresh
    ltac:(apply map_lookup_insert)
    Hlc_vself Hres_my Hfun_basic Hstatic_app Happ_src_mid) as Htarget_alias.
  change (my ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0)))).
  rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
      y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
      τ (erase_ty τx) (tret (vfvar z))).
  2:{ apply lty_env_closed_insert_free.
      subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst.
      clear -Hy_fresh. set_solver.
    - exfalso.
      subst Σrel efix τx Δ.
      pose proof (soundness_relevant_env_arrow_value_fresh
        (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
        vf y
        ltac:(cbn; clear -Hy_fresh; better_set_solver))
        as Hnot.
      exact (Hnot Hin).
  }
  2:{ cbn [fv_tm]. clear -Hy_fresh. set_solver. }
  2:{ clear -Hy_fresh. better_set_solver. }
  2:{ apply lc_ret_iff_value. constructor. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (Σ1 := <[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
        (<[LVFree y := erase_ty τx]> Δ))
      (X := relevant_lvars (cty_open 0 y τ)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  - reflexivity.
  - apply lam_lty_env_restrict_result_first_result_eq.
    + apply atom_store_to_lvar_store_closed.
    + eapply cty_lvars_open_body_closed_no_fresh.
      * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
      * intros HyD.
        apply lvars_fv_elem in HyD.
        rewrite context_ty_lvars_fv_at in HyD.
        clear -Hy_fresh HyD. better_set_solver.
      * reflexivity.
    + clear -Hy_fresh. set_solver.
    + clear -Hy_fresh. better_set_solver.
    + subst vself. cbn. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.

Lemma fundamental_value_arrow_case Σ Γ φx τ vf b (L : aset) :
  context_typing_wf Σ Γ (tret vf) (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (cty_open 0 y τ) (tapp_tm (tret vf) (vfvar y))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow (over_ty b φx) τ)
      (tret vf).
Proof.
  intros Hwf IH m Hctx.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (τx := over_ty b φx).
  set (vself := vf).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (CTArrow τx τ) (tret vself) m
    ltac:(subst τx vself; exact Hwf) Hctx) as Hstatic.
  pose proof (ty_denote_gas_zero_tret_of_static_guard
    Δ (CTArrow τx τ) vself m Hstatic) as Hzero.
  unfold ty_denote_under, ty_denote.
  change (m ⊨ ty_denote_gas (S gas) Δ (CTArrow τx τ) (tret vself)).
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - eapply ty_denote_gas_guard_of_zero. exact Hzero.
  - pose proof (ty_denote_gas_scope_from_zero_any
      (S gas) Δ (CTArrow τx τ) (tret vself) m Hzero)
      as Hscope_full.
    cbn [ty_denote_gas] in Hscope_full.
    apply (proj1 (formula_scoped_and_iff _ _ _)) in Hscope_full
      as [_ Hscope_body].
    eapply res_models_forall_rev_intro; [exact Hscope_body|].
    exists (L ∪ world_dom (m : WorldT) ∪ dom Σ ∪
      dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ).
    intros z Hz mz Hdomz Hrestrictz.
    assert (Hle_m_mz : m ⊑ mz).
    { rewrite <- Hrestrictz. apply res_restrict_le. }
    assert (Hz_world : z ∈ world_dom (mz : WorldT)).
    { rewrite Hdomz. apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
    pose proof (formula_scoped_forall_open_res_le
      m mz z _ Hscope_body Hle_m_mz Hz_world) as Hopened_scope.
    cbn [formula_open] in Hopened_scope |- *.
    eapply res_models_impl_intro; [exact Hopened_scope|].
    intros Hres_raw.
    assert (Hzfresh :
        z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
          fv_value vf ∪ fv_cty τx ∪ fv_cty τ).
    { clear -Hz. better_set_solver. }
    pose proof (value_result_first_outer_result_plain
      Σ Γ φx τ vf b mz z
      ltac:(subst τx vself; exact Hwf)
      ltac:(subst τx; clear -Hzfresh; better_set_solver)
      Hres_raw) as Hres_plain.
    assert (Hτx_lc : lc_context_ty τx).
    {
      subst τx vself.
      apply (context_typing_wf_arrow_arg_lc Σ Γ
        (tret vf) (over_ty b φx) τ).
      exact Hwf.
    }
    assert (Hτ_lc1 : cty_lc_at 1 τ).
    {
      subst τx vself.
      apply (context_typing_wf_arrow_result_lc1 Σ Γ
        (tret vf) (over_ty b φx) τ).
      exact Hwf.
    }
    assert (Hvalue_scope :
        formula_scoped_in_world mz
          (arrow_value_denote_gas_with ty_denote_gas gas
            (<[LVFree z := erase_ty (CTArrow τx τ)]>
              (relevant_env Δ (CTArrow τx τ) (tret vself)))
            τx τ (tret (vfvar z)))).
    {
      pose proof (formula_scoped_impl_r _ _ _ Hopened_scope) as Hraw.
      change (formula_scoped_in_world mz
        (formula_open 0 z
          (arrow_value_denote_gas_with ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Δ (CTArrow τx τ) (tret vself))
              (erase_ty (CTArrow τx τ)))
            (cty_shift 0 τx) (cty_shift 1 τ)
            (tret (vbvar 0))))) in Hraw.
      rewrite (formula_open_result_first_arrow_value_ret_bvar0
        gas (relevant_env Δ (CTArrow τx τ) (tret vself))
        τx τ (erase_ty (CTArrow τx τ)) z) in Hraw.
      - exact Hraw.
      - subst Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
      - subst Δ vself τx.
        eapply relevant_env_arrow_fresh_free.
        + clear -Hzfresh. better_set_solver.
        + clear -Hzfresh. better_set_solver.
        + cbn [fv_tm]. clear -Hzfresh. better_set_solver.
      - exact Hτx_lc.
      - exact Hτ_lc1.
      - clear -Hzfresh. better_set_solver.
      - clear -Hzfresh. better_set_solver.
    }
    change (mz ⊨ formula_open 0 z
      (arrow_value_denote_gas_with ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Δ (CTArrow τx τ) (tret vself))
          (erase_ty (CTArrow τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ)
        (tret (vbvar 0)))).
    rewrite (formula_open_result_first_arrow_value_ret_bvar0
      gas (relevant_env Δ (CTArrow τx τ) (tret vself))
      τx τ (erase_ty (CTArrow τx τ)) z).
    2:{ subst Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
    2:{
      subst Δ vself τx.
      eapply relevant_env_arrow_fresh_free.
      - clear -Hzfresh. better_set_solver.
      - clear -Hzfresh. better_set_solver.
      - cbn [fv_tm]. clear -Hzfresh. better_set_solver.
    }
    2:{ exact Hτx_lc. }
    2:{ exact Hτ_lc1. }
    2:{ clear -Hzfresh. better_set_solver. }
    2:{ clear -Hzfresh. better_set_solver. }
    eapply (value_result_first_arrow_value_denotation
      Σ Γ φx τ vf b L m mz z).
    + exact Hwf.
    + exact IH.
    + exact Hctx.
    + exact Hdomz.
    + exact Hrestrictz.
    + subst τx. exact Hzfresh.
    + exact Hvalue_scope.
    + exact Hres_plain.
Qed.
