(** * ContextTyping.SoundnessWandIntro

    Soundness of value introduction for the independent arrow. *)

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

Lemma value_wand_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ funval
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret funval) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value funval ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret funval) (vfvar y)).
Proof.
  intros Hwf Hy Hctx_star.
  assert (Hwf_app :
      context_typing_wf Σ (CtxStar Γ (CtxBind y τx))
        (tapp_tm (tret funval) (vfvar y))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ Γ
      (tret funval) (CTWand τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret funval) (CTWand τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx Hτ].
    split.
    + unfold wf_ctx_under. cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
      * apply basic_ctx_bind.
        -- ctx_erasure_under_norm_in Hy. better_set_solver.
        -- eapply (wf_context_ty_at_mono_env
             0 ∅ (dom Σ)).
           ++ better_set_solver.
           ++ exact Hτx.
      * cbn [ctx_dom]. ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ.
        better_set_solver.
    + split.
      * eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxStar Γ (CtxBind y τx))))).
        -- rewrite erase_ctx_star_bind_dom. reflexivity.
        -- apply wf_context_ty_at_open_at.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact Hτ.
      * rewrite cty_open_preserves_erasure.
        replace (erase_ctx (CtxStar Γ (CtxBind y τx)))
          with (<[y := erase_ty τx]> (erase_ctx Γ)).
        -- apply basic_typing_tapp_tm_fvar_insert.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact (context_typing_wf_basic_typing Σ Γ
                (tret funval) (CTWand τx τ) Hwf).
        -- symmetry. apply erase_ctx_star_bind_fresh.
           ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  pose proof (context_typing_wf_denot_static_guard_full
    Σ (CtxStar Γ (CtxBind y τx)) (cty_open 0 y τ)
    (tapp_tm (tret funval) (vfvar y))
    my Hwf_app Hctx_star) as Hstatic.
  assert (Henv :
      atom_env_to_lty_env (erase_ctx (CtxStar Γ (CtxBind y τx))) =
      (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))).
  {
    rewrite erase_ctx_star_bind_fresh.
    - apply atom_store_to_lvar_store_insert.
    - ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  rewrite Henv in Hstatic.
  exact Hstatic.
Qed.

Lemma value_wand_result_first_outer_result_plain
    (Σ : tyctx) Γ τx τ funval
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret funval) (CTWand τx τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value funval ∪ fv_cty τx ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret funval))))
      (tm_shift 0 (tret funval)) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret funval) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret funval))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret funval))))).
      {
        rewrite lvars_shift_from_fv.
        intros Hzbad.
        apply lvars_fv_elem in Hzbad.
        pose proof (soundness_relevant_env_wand_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) τx τ
          funval z
          ltac:(cbn [fv_value]; clear -Hz; better_set_solver))
          as Hnot.
        exact (Hnot Hzbad).
      }
  assert (Hlc_elam :
      lc_tm (tret funval)).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret funval) (CTWand τx τ) Hwf).
  }
  assert (Hz_elam :
      z ∉ fv_tm (tret funval)).
  {
    cbn [fv_tm fv_value].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_elam || exact Hz_elam).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret funval)))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret funval))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret funval)))).
  - intros v Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret funval) (CTWand τx τ) Hwf)
        as Hfv.
      destruct v as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret funval) (CTWand τx τ) Hwf)
          as Hlc.
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
        pose proof (soundness_relevant_env_wand_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) τx τ
          funval z
          ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
        exact (Hnot Hzbad).
  - exact Hres.
Qed.

Lemma value_wand_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ funval
    (n : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret funval) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value funval ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  n ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env
      (<[y := erase_ty τx]> (store_restrict Σ (fv_cty τx))))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret funval) τx τ Hwf) as Hτx_global.
  rewrite ty_denote_gas_saturate in Harg by lia.
  eapply ty_denote_gas_ret_fvar_insert_closed_atom_env; eauto.
Qed.

Lemma value_wand_open_arg_to_star_ctx
    (Σ : tyctx) Γ τx τ funval
    (m n : WfWorldT) y (Hc : world_compat n m) :
  context_typing_wf Σ Γ
    (tret funval) (CTWand τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value funval ∪ fv_cty τx ∪ fv_cty τ ->
    n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
        τx (tret (vfvar y)) ->
    res_product n m Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)).
  Proof.
  intros Hwf Hctx Hdom Hy Harg.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret funval) τx τ Hwf) as Hτx_global.
  pose proof (value_wand_open_arg_to_bind_denotation
    Σ Γ τx τ funval n y Hwf Hy Harg) as Harg_den.
  assert (Hbind_cropped :
      n ⊨ ctx_denote_under (store_restrict Σ (fv_cty τx))
        (CtxBind y τx)).
  {
    eapply ctx_bind_from_base_denotation.
    - eapply wf_context_ty_at_mono_env; [|exact Hτx_global].
      better_set_solver.
    - intros HyΣ.
      apply Hy.
      rewrite storeA_restrict_dom in HyΣ.
      better_set_solver.
    - exact Harg_den.
  }
  assert (Hbind : n ⊨ ctx_denote_under Σ (CtxBind y τx)).
  {
    rewrite ctx_denote_under_minimal.
    exact Hbind_cropped.
  }
  pose proof (context_typing_wf_ctx Σ Γ
    (tret funval) (CTWand τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  destruct (res_product_comm_eq n m Hc) as [Hcmn Heq].
  rewrite Heq.
  eapply ctx_denote_under_star_intro_product; eauto.
Qed.

Lemma value_result_first_wand_value_denotation
    (Σ : tyctx) Γ τx τ funval (L : aset)
    (m mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret funval) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (tapp_tm (tret funval) (vfvar y))) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value funval ∪ fv_cty τx ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (wand_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree z := erase_ty (CTWand τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret funval)))
      τx τ (tret (vfvar z))) ->
  mz ⊨ expr_result_formula (tret funval) (LVFree z) ->
  mz ⊨ wand_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree z := erase_ty (CTWand τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret funval)))
      τx τ (tret (vfvar z)).
Proof.
  intros Hwf IH Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (vf := funval).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTWand τx τ) (tret vf)).
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (context_typing_wf_context_ty
    Σ Γ (tret funval) (CTWand τx τ) Hwf)
    as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  cbn [wand_value_denote_gas_with] in Hscope_value |- *.
  eapply res_models_fbwand_intro; [exact Hscope_value|].
  exists (L ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_value funval ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  intros η n Hc Hbind Hηfresh Hdom_prod Harg_raw.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
  rewrite formula_open_env_singleton in Harg_raw |- *.
  rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
  rewrite open_env_atoms_empty in Hηfresh.
  rewrite open_env_atoms_insert in Hdom_prod by apply lookup_empty.
  rewrite open_env_atoms_empty in Hdom_prod.
    assert (Hdom_y :
        world_dom (res_product n mz Hc : WorldT) =
          world_dom (mz : WorldT) ∪ ({[y]} : aset)).
    {
      rewrite Hdom_prod. apply union_singleton_empty_r.
    }
  assert (Hy_fresh :
      y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value funval ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  {
    clear -Hηfresh. set_solver.
  }
    assert (Hy_rest :
        y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
          fv_value funval ∪ fv_cty τx ∪ fv_cty τ).
    { clear -Hy_fresh. better_set_solver. }
      assert (Hy_eraseΓ : y ∉ dom (erase_ctx Γ)).
      { eapply soundness_fresh_erase_ctx_from_context_union. exact Hy_rest. }
    assert (HyΔ : LVFree y ∉ dom Δ).
    {
      subst Δ. apply atom_env_to_lty_env_dom_free_notin.
      exact Hy_eraseΓ.
    }
    assert (HyL : y ∉ L) by (clear -Hy_fresh; better_set_solver).
  assert (Hyz : y <> z) by (clear -Hy_fresh; set_solver).
  assert (Harg_norm :
      n ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        τx (tret (vfvar y))).
  {
    change (n ⊨ formula_open 0 y
      (ty_denote_gas gas
        (typed_lty_env_bind
          (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel)
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) in Harg_raw.
    rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
      y gas (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel) τx)
      in Harg_raw.
    - exact Harg_raw.
    - apply lty_env_closed_insert_free.
      subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
    - rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hyz. congruence.
      + subst Σrel. apply relevant_env_wand_fresh_free in Hin;
          cbn [fv_tm fv_value]; clear -Hy_fresh Hin; better_set_solver.
    - clear -Hy_fresh. better_set_solver.
    - exact Hτx_lc.
  }
    assert (Harg_old :
        n ⊨ ty_denote_gas gas
          (<[LVFree y := erase_ty τx]> Δ)
          τx (tret (vfvar y))).
    {
      eapply res_models_ty_denote_gas_env_agree_on
        with (Σ1 := <[LVFree y := erase_ty τx]>
        (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - rewrite lty_env_insert_free_commute by exact Hyz.
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy_fresh Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTWand τx τ)) Hz_rel_arg).
      apply lamd_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst vf. clear -Hy_fresh. cbn [fv_value]. better_set_solver.
    - exact Harg_norm.
  }
  assert (Hctx_star :
        res_product n mz Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx))).
    {
      eapply (value_wand_open_arg_to_star_ctx Σ Γ τx τ funval mz n y Hc).
      - exact Hwf.
      - exact Hctx_mz.
      - exact Hdom_y.
      - exact Hy_rest.
      - exact Harg_old.
    }
  assert (Hsrc :
      res_product n mz Hc ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        (cty_open 0 y τ) (tapp_tm (tret vf) (vfvar y))).
  {
    pose proof (IH y HyL (res_product n mz Hc) Hctx_star) as Hcall.
    unfold ty_denote_under, ty_denote in Hcall.
    rewrite erase_ctx_star_bind_fresh in Hcall by exact Hy_eraseΓ.
    change (res_product n mz Hc ⊨ ty_denote_gas (cty_depth (cty_open 0 y τ))
      (atom_env_to_lty_env (<[y:=erase_ty τx]> (erase_ctx Γ)))
      (cty_open 0 y τ) (tapp_tm (tret funval) (vfvar y))) in Hcall.
    assert (Henv : atom_env_to_lty_env (<[y:=erase_ty τx]> (erase_ctx Γ)) =
      <[LVFree y:=erase_ty τx]> Δ).
    { subst Δ. apply atom_store_to_lvar_store_insert. }
    rewrite <- Henv.
    rewrite ty_denote_gas_saturate by (rewrite cty_open_preserves_depth; subst gas; lia).
    exact Hcall.
  }
  pose proof (value_wand_opened_app_static_guard_full
    Σ Γ τx τ funval (res_product n mz Hc) y
    Hwf Hy_rest Hctx_star) as Hstatic_app.
  assert (Hres_prod :
      res_product n mz Hc ⊨ expr_result_formula (tret vf) (LVFree z)).
  {
    subst vf.
    eapply res_models_kripke; [apply res_product_le_r|exact Hres_z].
  }
  assert (Hfun_basic :
      res_product n mz Hc ⊨ expr_basic_typing_formula
        (<[LVFree y := erase_ty τx]> Δ)
        (tret vf) (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
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
        * subst Δ vf.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret funval) (CTWand τx τ) Hwf).
          * apply insert_subseteq. apply not_elem_of_dom.
            exact HyΔ.
  }
  assert (Hlc_vf : lc_value vf).
  {
    subst vf.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret funval) (CTWand τx τ) Hwf).
  }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    subst Δ. apply
      (ctx_erasure_under_inserted_erase_ctx_lty_env_fresh
        Σ Γ z y (erase_ty τx)).
    - clear -Hyz. congruence.
    - clear -Hz. better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value vf ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
  {
    apply value_open_result_alias_fresh.
    subst vf. cbn [fv_value].
    clear -Hy_fresh Hz Hyz. better_set_solver.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
    vf y z (erase_ty τx) (res_product n mz Hc)
    Hz_insert_env
    Hz_alias_fresh
    ltac:(apply map_lookup_insert)
    Hlc_vf
    Hres_prod Hfun_basic Hstatic_app Hsrc) as Htarget_alias.
  change (res_product n mz Hc ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel)
        (erase_ty τx))
      τ (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0)))).
  rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
    y gas (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel)
    τ (erase_ty τx) (tret (vfvar z))).
  2:{
    apply lty_env_closed_insert_free.
    subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hyz. congruence.
    - subst Σrel. apply relevant_env_wand_fresh_free in Hin;
        cbn [fv_tm fv_value]; clear -Hy_fresh Hin; better_set_solver.
  }
  2:{ cbn [fv_tm fv_value]. clear -Hyz. set_solver. }
  2:{ clear -Hy_fresh. better_set_solver. }
  2:{ constructor. constructor. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (Σ1 := <[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
        (<[LVFree y := erase_ty τx]> Δ))
      (X := relevant_lvars (cty_open 0 y τ)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  - reflexivity.
  - apply lamd_lty_env_restrict_result_first_result_eq.
    + apply atom_store_to_lvar_store_closed.
    + eapply cty_lvars_open_body_closed_no_fresh.
      * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
      * intros HyD.
        apply lvars_fv_elem in HyD.
        rewrite context_ty_lvars_fv_at in HyD.
        clear -Hy_rest HyD. better_set_solver.
      * reflexivity.
    + exact Hyz.
    + clear -Hy_rest. better_set_solver.
    + subst vf. cbn [fv_value]. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.

Lemma value_wand_observed_vars_world_dom
    (Σ : gmap atom ty) Γ e τ (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  fv_tm e ∪ fv_cty τ ⊆ world_dom (m : WorldT).
Proof.
  intros Hwf Hctx a Ha.
  pose proof (context_typing_wf_fv_tm_subset Σ Γ e τ Hwf) as Htm.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ Hwf) as Hτfv.
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m Hworld) as Hdom.
  apply Hdom.
  apply ctx_erasure_under_erase_ctx_dom_subset.
  apply elem_of_union in Ha as [Ha | Ha].
  - exact (Htm a Ha).
  - exact (Hτfv a Ha).
Qed.

Lemma fundamental_value_wand_case Σ Γ τx τ funval (L : aset) :
  context_typing_wf Σ Γ (tret funval) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (tapp_tm (tret funval) (vfvar y))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTWand τx τ)
      (tret funval).
Proof.
  intros Hwf IH m Hctx.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (vf := funval).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (CTWand τx τ) (tret vf) m Hwf Hctx) as Hstatic.
  pose proof (ty_denote_gas_zero_tret_of_static_guard
    Δ (CTWand τx τ) vf m Hstatic) as Hzero.
  unfold ty_denote_under, ty_denote.
  change (m ⊨ ty_denote_gas (S gas) Δ (CTWand τx τ) (tret vf)).
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - eapply ty_denote_gas_guard_of_zero. exact Hzero.
  - pose proof (ty_denote_gas_scope_from_zero_any
      (S gas) Δ (CTWand τx τ) (tret vf) m Hzero) as Hscope_full.
    cbn [ty_denote_gas] in Hscope_full.
    apply (proj1 (formula_scoped_and_iff _ _ _)) in Hscope_full
      as [_ Hscope_body].
    eapply res_models_forall_rev_intro; [exact Hscope_body|].
    exists (L ∪ world_dom (m : WorldT) ∪ dom Σ ∪
      dom (ctx_erasure_under Σ Γ) ∪ fv_value funval ∪ fv_cty τx ∪ fv_cty τ).
    intros z Hz mz Hdomz Hrestrictz.
    assert (Hle_m_mz : m ⊑ mz).
    { rewrite <- Hrestrictz. apply res_restrict_le. }
    assert (Hz_world : z ∈ world_dom (mz : WorldT)).
    { rewrite Hdomz. set_solver. }
    pose proof (formula_scoped_forall_open_res_le
      m mz z _ Hscope_body Hle_m_mz Hz_world) as Hopened_scope.
    cbn [formula_open] in Hopened_scope |- *.
    eapply res_models_impl_intro; [exact Hopened_scope|].
    intros Hres_raw.
    assert (Hzfresh :
        z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
          fv_value funval ∪ fv_cty τx ∪ fv_cty τ).
    { clear -Hz. better_set_solver. }
      pose proof (value_wand_result_first_outer_result_plain
        Σ Γ τx τ funval mz z Hwf
        ltac:(clear -Hzfresh; better_set_solver) Hres_raw) as Hres_plain.
      assert (Hscope_value_norm :
          formula_scoped_in_world mz
            (wand_value_denote_gas_with ty_denote_gas gas
              (<[LVFree z := erase_ty (CTWand τx τ)]>
                (relevant_env Δ (CTWand τx τ) (tret vf)))
              τx τ (tret (vfvar z)))).
      {
        eapply formula_scoped_wand_value_body_obs.
        rewrite Hdomz.
        pose proof (value_wand_observed_vars_world_dom
          Σ Γ (tret vf) (CTWand τx τ) m Hwf Hctx) as Hobs.
        cbn [fv_tm fv_value fv_cty] in Hobs.
        clear -Hobs. set_solver.
      }
      change (mz ⊨ formula_open 0 z
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Δ (CTWand τx τ) (tret vf))
            (erase_ty (CTWand τx τ)))
          (cty_shift 0 τx) (cty_shift 1 τ)
          (tret (vbvar 0)))).
      rewrite (formula_open_result_first_wand_value_ret_bvar0
        gas (relevant_env Δ (CTWand τx τ) (tret vf))
        τx τ (erase_ty (CTWand τx τ)) z).
      2:{
        apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
      }
      2:{
        apply soundness_relevant_env_wand_value_fresh.
        clear -Hzfresh. better_set_solver.
      }
      2:{
        pose proof (context_typing_wf_context_ty
          Σ Γ (tret vf) (CTWand τx τ) Hwf) as Hτwf.
        cbn [wf_context_ty_at] in Hτwf.
        eapply wf_context_ty_at_lc. exact (proj1 Hτwf).
      }
      2:{
        pose proof (context_typing_wf_context_ty
          Σ Γ (tret vf) (CTWand τx τ) Hwf) as Hτwf.
        cbn [wf_context_ty_at] in Hτwf.
        eapply wf_context_ty_at_lc. exact (proj2 Hτwf).
      }
      2:{ clear -Hzfresh. better_set_solver. }
      2:{ clear -Hzfresh. better_set_solver. }
      eapply (value_result_first_wand_value_denotation
        Σ Γ τx τ funval L m mz z);
        [ exact Hwf
        | exact IH
        | exact Hctx
        | exact Hdomz
        | exact Hrestrictz
        | exact Hzfresh
        | exact Hscope_value_norm
        | exact Hres_plain ].
Qed.
