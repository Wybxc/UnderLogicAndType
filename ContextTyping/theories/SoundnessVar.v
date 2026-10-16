(** * Variable lookup in dependent additive contexts. *)
From CoreLang Require Import BasicTyping BasicTypingProps.
From ContextTypeLanguage Require Import WF.
From Denotation Require Import Context TypeEquiv.
From ContextBase Require Import BaseTactics.
From Denotation Require Import ConstDenote ConstDenoteBase.
From Denotation Require Import TypeEquivFiberBaseCore.
From Denotation Require Import TypeEquivCore TypePersistBase ResultFirstOpen.
From ContextTyping Require Import Typing TypingRegular.
From ContextTyping Require Import SoundnessLam.

Lemma denot_var_right_in_ctx Σ Γ x τ :
  context_typing_wf Σ (CtxComma Γ (CtxBind x τ)) (tret (vfvar x)) τ ->
  ctx_denote_under Σ (CtxComma Γ (CtxBind x τ)) ⊫
    ty_denote_under Σ (CtxComma Γ (CtxBind x τ)) τ (tret (vfvar x)).
Proof.
  intros Hwf m Hctx.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf) as Hfv.
  pose proof (context_typing_wf_ctx _ _ _ _ Hwf) as Hbasic.
  unfold wf_ctx_under in Hbasic.
  cbn [basic_ctx] in Hbasic.
  destruct Hbasic as [HΓ [Hbind Hdisj]].
  pose proof (basic_ctx_erase_dom (dom Σ) Γ HΓ) as Hdom.
  assert (Hx : x ∉ dom (erase_ctx Γ)).
  { rewrite Hdom. cbn [ctx_dom] in Hdisj. set_solver. }
  cbn [ctx_denote_under] in Hctx.
  apply res_models_and_iff in Hctx as [_ Hctx].
  apply res_models_and_iff in Hctx as [_ Hright].
  apply res_models_and_iff in Hright as [_ Hden].
  unfold ty_denote_under, ty_denote in *.
  rewrite erase_ctx_comma_bind_fresh by exact Hx.
  eapply ty_denote_gas_ret_fvar_insert_atom_env_agree_on; [|exact Hden].
  intros z Hz.
  unfold store_insert.
  destruct (decide (z = x)) as [->|Hzx].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    assert (Hzτ : z ∈ fv_cty τ) by set_solver.
    assert (HzΓ : z ∈ dom (erase_ctx Γ)).
    { specialize (Hfv z Hzτ). rewrite erase_ctx_comma_bind_dom in Hfv. set_solver. }
    apply elem_of_dom in HzΓ as [T HT].
    rewrite HT.
    eapply storeA_restrict_lookup_some_2.
    + apply map_lookup_union_Some_raw. right. split; [|exact HT].
      apply storeA_restrict_lookup_none_l.
      apply (basic_ctx_erase_dom_fresh_none Σ Γ z HΓ).
      apply elem_of_dom. eauto.
    + cbn [ctx_fv]. exact Hzτ.
Qed.

Local Lemma var_typed_qual_open_msubst b x y σ c :
  x <> y -> dom (σ : gmap atom value) = {[x]} ->
  σ !! x = Some (vconst c) -> base_ty_of_const c = b ->
  qual_msubst_store σ
    (qual_open_atom 0 y (typed_result_qual b
      (mk_q_eq (vbvar 0) (vfvar x)))) =
  mk_q_eq (vfvar y) (vconst c).
Proof.
  intros Hxy Hdom Hx Hb.
  assert (Hρdom : dom (atom_store_to_lvar_store σ : gmap logic_var value) =
      {[LVFree x]}).
  { rewrite atom_store_to_lvar_store_dom, Hdom.
    unfold lvars_of_atoms. rewrite set_map_singleton_L. reflexivity. }
  apply qual_ext.
  - cbn [qual_msubst_store qual_mlsubst qual_open_atom typed_result_qual
      mk_q_eq qual_lvars qual_vars lvar_value_keys].
    rewrite Hρdom.
    rewrite !set_swap_union, !set_swap_singleton.
    base_swap_normalize. set_solver.
  - intros [s1 Hdom1] [s2 Hdom2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [qual_msubst_store qual_mlsubst qual_open_atom typed_result_qual
      mk_q_eq qual_prop qual_lvars qual_vars lvar_value_keys denote_lvar_value].
    unfold lstore_on_restrict, storeA_on_restrict, lstore_on_open_back,
      lstore_on_mlsubst_back.
    cbn [lso_store storeAO_store].
    unfold lstore_lookup.
    cbn [lookup].
    rewrite !(@storeA_restrict_lookup value logic_var logic_var_eqdec logic_var_countable).
    rewrite !decide_True by set_solver.
    unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !lstore_swap_lookup_inv_value. base_swap_normalize.
    unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
    assert (Hs1x : s1 !! LVFree x = None).
    { apply not_elem_of_dom. rewrite Hdom1.
      cbn [qual_msubst_store qual_mlsubst qual_open_atom typed_result_qual
        mk_q_eq qual_lvars qual_vars lvar_value_keys].
      rewrite Hρdom. set_solver. }
    assert (Hs1y : LVFree y ∈ dom s1).
    { rewrite Hdom1.
      cbn [qual_msubst_store qual_mlsubst qual_open_atom typed_result_qual
        mk_q_eq qual_lvars qual_vars lvar_value_keys].
      rewrite Hρdom. rewrite !set_swap_union, !set_swap_singleton.
      base_swap_normalize. set_solver. }
    set (D := ({[LVFree y; LVFree x; LVFree y]} : lvset)).
    assert (Hlookx :
      (s1 ∪ storeA_restrict (atom_store_to_lvar_store σ) D) !! LVFree x =
      Some (vconst c)).
    { apply map_lookup_union_Some_raw. right. split; [exact Hs1x|].
      apply storeA_restrict_lookup_some_2.
      - rewrite atom_store_to_lvar_store_lookup_free. exact Hx.
      - subst D. set_solver. }
    assert (Hlooky :
      (s1 ∪ storeA_restrict (atom_store_to_lvar_store σ) D) !! LVFree y =
      s1 !! LVFree y).
    { apply lookup_union_l'. apply elem_of_dom. exact Hs1y. }
    change (
      ((s1 ∪ storeA_restrict (atom_store_to_lvar_store σ) D) !! LVFree y =
       (s1 ∪ storeA_restrict (atom_store_to_lvar_store σ) D) !! LVFree x /\
       exists v,
         (s1 ∪ storeA_restrict (atom_store_to_lvar_store σ) D) !! LVFree y = Some v /\
         basic_value_has_ltype ∅ v (TBase b)) <->
      s2 !! LVFree y = Some (vconst c)).
    rewrite Hlookx, Hlooky.
    rewrite Hs. split.
    + intros [Heq _]. exact Heq.
    + intros Heq. split; [exact Heq|].
      exists (vconst c). split; [exact Heq|].
      rewrite <- Hb. constructor.
Qed.

(** Reading an earlier additive binding needs no new primitive rule: drop
    later bindings by the existing context-subsumption rule. *)
Lemma typing_weaken_comma Φ Σ Γ Γ' e τ :
  context_typing_wf Σ (CtxComma Γ Γ') e τ ->
  has_context_type Φ Σ Γ e τ ->
  has_context_type Φ Σ (CtxComma Γ Γ') e τ.
Proof.
  intros Hwf Hty.
  eapply CT_CtxSub; [exact Hwf | exact Hty |].
  unfold ctx_sub_under.
  pose proof (typing_wf_under _ _ _ _ _ Hty) as Hprefix.
  split; [exact (context_typing_wf_ctx _ _ _ _ Hwf)|].
  split; [exact (context_typing_wf_ctx _ _ _ _ Hprefix)|].
  split.
  - intros x Hx.
    assert (HxΓ : x ∈ dom (erase_ctx Γ)).
    { apply elem_of_union in Hx as [He|Hτ].
      - eapply context_typing_wf_fv_tm_subset; eauto.
      - eapply context_typing_wf_fv_cty_subset_erase_dom; eauto. }
    apply elem_of_dom in HxΓ as [T HT].
    change ((erase_ctx Γ ∪ erase_ctx Γ') !! x = erase_ctx Γ !! x).
    rewrite HT. apply map_lookup_union_Some_raw. left. exact HT.
  - intros m Hctx. exists m. split.
    + apply res_restrict_le.
    + eapply ctx_denote_under_comma_left; exact Hctx.
Qed.

Local Lemma var_typed_result_fiber b x y (m : WfWorld (V := value)) :
  x <> y ->
  (forall σ, (m : World (V := value)) σ ->
    exists c, σ !! x = Some (vconst c) /\ base_ty_of_const c = b) ->
  m ⊨ expr_result_formula (tret (vfvar x)) (LVFree y) ->
  m ⊨ FFibVars {[LVFree x]}
    (FAtom (qual_open_atom 0 y
      (typed_result_qual b (mk_q_eq (vbvar 0) (vfvar x))))).
Proof.
  intros Hxy Htyped Hres.
  pose proof (res_models_scoped _ _ Hres) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  rewrite formula_fv_expr_result_formula in Hscope.
  cbn [tm_lvars tm_lvars_at value_lvars_at] in Hscope.
  assert (Hvars : qual_vars (qual_open_atom 0 y
      (typed_result_qual b (mk_q_eq (vbvar 0) (vfvar x)))) =
      ({[LVFree y; LVFree x; LVFree y]} : lvset)).
  { cbn [qual_open_atom typed_result_qual mk_q_eq qual_vars qual_lvars
      lvar_value_keys].
    rewrite !set_swap_union, !set_swap_singleton.
    base_swap_normalize. reflexivity. }
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_fibvars, formula_fv_atom.
    unfold qual_dom. rewrite Hvars.
    rewrite !lvars_fv_union, !lvars_fv_singleton_free in *.
    set_solver.
  - intros [k|z] Hz; cbn [lc_logic_var_key]; [set_solver|exact I].
  - intros σ mfib Hproj.
    rewrite lvars_fv_singleton_free in Hproj.
    assert (Hdom : dom (σ : gmap atom value) = {[x]}).
    { pose proof (wfworld_store_dom (res_restrict m {[x]}) σ (proj1 Hproj)) as Hd.
      rewrite res_restrict_dom in Hd.
      rewrite lvars_fv_union, !lvars_fv_singleton_free in Hscope.
      set_solver. }
    destruct (world_wf mfib) as [[σ0 Hσ0] _].
    pose proof (res_fiber_from_projection_store_source _ _ _ _ _ Hproj Hσ0) as Hσ0m.
    destruct (Htyped σ0 Hσ0m) as [c [Hc Hbase]].
    pose proof (res_fiber_from_projection_store_restrict _ _ _ _ _ Hproj Hσ0) as Hr.
    assert (Hσx : σ !! x = Some (vconst c)).
    { rewrite <- Hr. apply storeA_restrict_lookup_some_2; [exact Hc|].
      rewrite Hdom. set_solver. }
    change (mfib ⊨ FAtom (qual_msubst_store σ
      (qual_open_atom 0 y (typed_result_qual b
        (mk_q_eq (vbvar 0) (vfvar x)))))).
    rewrite (var_typed_qual_open_msubst b x y σ c Hxy Hdom Hσx Hbase).
    apply const_type_qualifier_open_from_lookup.
    intros σ1 Hσ1.
    pose proof (res_fiber_from_projection_store_source _ _ _ _ _ Hproj Hσ1) as Hσ1m.
    pose proof (expr_result_formula_at_models_elim
      {[LVFree x]} (tret (vfvar x)) y m ltac:(cbn; set_solver)
      ltac:(set_solver) Hres σ1 Hσ1m) as Hresult.
    destruct Hresult as [_ [v [Hy Heval]]].
    rewrite lstore_lift_free_lookup_free in Hy.
    pose proof (res_fiber_from_projection_store_restrict _ _ _ _ _ Hproj Hσ1) as Hr1.
    assert (Hσ1x : σ1 !! x = Some (vconst c)).
    { pose proof Hσx as Hl. rewrite <- Hr1 in Hl.
      apply storeA_restrict_lookup_some in Hl as [_ Hl]. exact Hl. }
    unfold expr_eval_in_store, lstore_instantiate_tm, lstore_instantiate_tm_at in Heval.
    cbn [lstore_instantiate_tm_at lstore_instantiate_value_at] in Heval.
    rewrite lstore_free_part_lift_free in Heval.
    cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at] in Heval.
    change (steps (tret (match σ1 !! x with Some u => u | None => vfvar x end))
      (tret v)) in Heval.
    rewrite Hσ1x in Heval. apply val_steps_self in Heval.
    inversion Heval; subst v. exact Hy.
Qed.

Local Lemma var_over_denotation_gas gas Σ b x (m : WfWorld (V := value)) :
  m ⊨ ty_denote_gas 0 Σ (CTOver b (mk_q_eq (vbvar 0) (vfvar x)))
    (tret (vfvar x)) ->
  m ⊨ ty_denote_gas gas Σ (CTOver b (mk_q_eq (vbvar 0) (vfvar x)))
    (tret (vfvar x)).
Proof.
  set (τ := CTOver b (mk_q_eq (vbvar 0) (vfvar x))).
  set (e := tret (vfvar x)).
  intros Hzero. destruct gas as [|gas]; [exact Hzero|].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ τ e m Hzero) as Hscope.
  pose proof (formula_scoped_and_r _ _ _ Hscope) as Hscope_all.
  pose proof (ty_denote_gas_zero_lc_relevant_env Σ τ e m Hzero) as HlcD.
  pose proof (ty_denote_gas_zero_tm_lvars_dom Σ τ e m Hzero) as HeD.
  cbn [ty_denote_gas]. apply res_models_and_iff. split.
  - exact (ty_denote_gas_guard_of_zero Σ τ e m Hzero).
  - eapply res_models_forall_rev_intro; [exact Hscope_all|].
    exists (lvars_fv (dom (relevant_env Σ τ e)) ∪ {[x]}).
    intros y Hy my Hdom Hrestrict.
    assert (HyD : y ∉ lvars_fv (dom (relevant_env Σ τ e))) by set_solver.
    assert (HyDlv : LVFree y ∉ dom (relevant_env Σ τ e)).
    { intros Hin. apply HyD. apply lvars_fv_elem. exact Hin. }
    assert (Hxy : x <> y) by set_solver.
    assert (Hle : m ⊑ my) by (eapply res_le_of_projection_eq; exact Hrestrict).
    assert (Hiny : y ∈ world_dom (my : World (V := value))) by (rewrite Hdom; set_solver).
    pose proof (formula_scoped_forall_open_res_le m my y _
      Hscope_all Hle Hiny) as Hscope_open.
    unfold τ, e in *.
    rewrite !formula_open_impl in Hscope_open |- *.
    fold (over_result_body b (mk_q_eq (vbvar 0) (vfvar x))) in Hscope_open |- *.
    rewrite formula_open_over_typed_body_normalize in Hscope_open |- *.
    2,3: cbn [mk_q_eq qual_vars qual_lvars lvar_value_keys]; set_solver.
    eapply res_models_impl_intro; [exact Hscope_open|].
    intros Hres.
    rewrite (formula_open_result_first_expr_result_formula_at_shift0
      y (dom (relevant_env Σ
        (CTOver b (mk_q_eq (vbvar 0) (vfvar x))) (tret (vfvar x))))
      (tret (vfvar x)) HlcD HyD ltac:(constructor; constructor)
      ltac:(cbn; set_solver)) in Hres.
    pose proof (expr_result_formula_at_coarsen_domain
      (tm_lvars (tret (vfvar x)))
      (dom (relevant_env Σ (CTOver b (mk_q_eq (vbvar 0) (vfvar x)))
        (tret (vfvar x))))
      (tret (vfvar x)) y my HeD ltac:(cbn; set_solver) HyDlv Hres) as Hsmall.
    assert (Htyped : forall σ, (my : World (V := value)) σ ->
        exists c, σ !! x = Some (vconst c) /\ base_ty_of_const c = b).
    { eapply ty_denote_ret_fvar_base_const with (gas := 0) (Σ := Σ)
        (τ := CTOver b (mk_q_eq (vbvar 0) (vfvar x))).
      - reflexivity.
      - eapply res_models_kripke; [exact Hle|exact Hzero]. }
    pose proof (var_typed_result_fiber b x y my Hxy Htyped Hsmall) as Hatom.
    unfold over_open_body.
    replace (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vfvar x)))
      ∖ {[LVFree y]}) with ({[LVFree x]} : lvset).
    2:{ cbn [qual_open_atom mk_q_eq qual_vars qual_lvars lvar_value_keys].
        rewrite !set_swap_union, !set_swap_singleton.
        base_swap_normalize. set_solver. }
    apply res_models_FFibVars_iff in Hatom as [Hsc [Hlc Hfib]].
    eapply res_models_FFibVars_intro.
    + unfold formula_scoped_in_world in *.
      rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
      rewrite formula_fv_fibvars, formula_fv_atom in Hsc. exact Hsc.
    + exact Hlc.
    + intros σ mfib Hproj.
      change (mfib ⊨ FOver (formula_msubst_store σ
        (FAtom (qual_open_atom 0 y (typed_result_qual b
          (mk_q_eq (vbvar 0) (vfvar x))))))).
      apply res_models_over_intro_same_from_model. exact (Hfib σ mfib Hproj).
Qed.

Local Lemma var_under_denotation_gas gas Σ b x (m : WfWorld (V := value)) :
  m ⊨ ty_denote_gas 0 Σ (CTUnder b (mk_q_eq (vbvar 0) (vfvar x)))
    (tret (vfvar x)) ->
  m ⊨ ty_denote_gas gas Σ (CTUnder b (mk_q_eq (vbvar 0) (vfvar x)))
    (tret (vfvar x)).
Proof.
  set (τ := CTUnder b (mk_q_eq (vbvar 0) (vfvar x))).
  set (e := tret (vfvar x)).
  intros Hzero. destruct gas as [|gas]; [exact Hzero|].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ τ e m Hzero) as Hscope.
  pose proof (formula_scoped_and_r _ _ _ Hscope) as Hscope_all.
  pose proof (ty_denote_gas_zero_lc_relevant_env Σ τ e m Hzero) as HlcD.
  pose proof (ty_denote_gas_zero_tm_lvars_dom Σ τ e m Hzero) as HeD.
  cbn [ty_denote_gas]. apply res_models_and_iff. split.
  - exact (ty_denote_gas_guard_of_zero Σ τ e m Hzero).
  - eapply res_models_forall_rev_intro; [exact Hscope_all|].
    exists (lvars_fv (dom (relevant_env Σ τ e)) ∪ {[x]}).
    intros y Hy my Hdom Hrestrict.
    assert (HyD : y ∉ lvars_fv (dom (relevant_env Σ τ e))) by set_solver.
    assert (HyDlv : LVFree y ∉ dom (relevant_env Σ τ e)).
    { intros Hin. apply HyD. apply lvars_fv_elem. exact Hin. }
    assert (Hxy : x <> y) by set_solver.
    assert (Hle : m ⊑ my) by (eapply res_le_of_projection_eq; exact Hrestrict).
    assert (Hiny : y ∈ world_dom (my : World (V := value))) by (rewrite Hdom; set_solver).
    pose proof (formula_scoped_forall_open_res_le m my y _
      Hscope_all Hle Hiny) as Hscope_open.
    unfold τ, e in *.
    rewrite !formula_open_impl in Hscope_open |- *.
    fold (under_result_body b (mk_q_eq (vbvar 0) (vfvar x))) in Hscope_open |- *.
    rewrite formula_open_under_typed_body_normalize in Hscope_open |- *.
    2,3: cbn [mk_q_eq qual_vars qual_lvars lvar_value_keys]; set_solver.
    eapply res_models_impl_intro; [exact Hscope_open|].
    intros Hres.
    rewrite (formula_open_result_first_expr_result_formula_at_shift0
      y (dom (relevant_env Σ
        (CTUnder b (mk_q_eq (vbvar 0) (vfvar x))) (tret (vfvar x))))
      (tret (vfvar x)) HlcD HyD ltac:(constructor; constructor)
      ltac:(cbn; set_solver)) in Hres.
    pose proof (expr_result_formula_at_coarsen_domain
      (tm_lvars (tret (vfvar x)))
      (dom (relevant_env Σ (CTUnder b (mk_q_eq (vbvar 0) (vfvar x)))
        (tret (vfvar x))))
      (tret (vfvar x)) y my HeD ltac:(cbn; set_solver) HyDlv Hres) as Hsmall.
    assert (Htyped : forall σ, (my : World (V := value)) σ ->
        exists c, σ !! x = Some (vconst c) /\ base_ty_of_const c = b).
    { eapply ty_denote_ret_fvar_base_const with (gas := 0) (Σ := Σ)
        (τ := CTUnder b (mk_q_eq (vbvar 0) (vfvar x))).
      - reflexivity.
      - eapply res_models_kripke; [exact Hle|exact Hzero]. }
    pose proof (var_typed_result_fiber b x y my Hxy Htyped Hsmall) as Hatom.
    unfold under_open_body.
    replace (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vfvar x)))
      ∖ {[LVFree y]}) with ({[LVFree x]} : lvset).
    2:{ cbn [qual_open_atom mk_q_eq qual_vars qual_lvars lvar_value_keys].
        rewrite !set_swap_union, !set_swap_singleton.
        base_swap_normalize. set_solver. }
    apply res_models_FFibVars_iff in Hatom as [Hsc [Hlc Hfib]].
    eapply res_models_FFibVars_intro.
    + unfold formula_scoped_in_world in *.
      rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
      rewrite formula_fv_fibvars, formula_fv_atom in Hsc. exact Hsc.
    + exact Hlc.
    + intros σ mfib Hproj.
      change (mfib ⊨ FUnder (formula_msubst_store σ
        (FAtom (qual_open_atom 0 y (typed_result_qual b
          (mk_q_eq (vbvar 0) (vfvar x))))))).
      apply res_models_under_intro_same_from_model. exact (Hfib σ mfib Hproj).
Qed.

Lemma denot_var_precise_in_ctx Σ Γ b x :
  context_typing_wf Σ Γ (tret (vfvar x))
    (precise_ty b (mk_q_eq (vbvar 0) (vfvar x))) ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ
    (precise_ty b (mk_q_eq (vbvar 0) (vfvar x))) (tret (vfvar x)).
Proof.
  intros Hwf m Hctx.
  pose proof (context_typing_wf_denot_static_guard_full Σ Γ
    (precise_ty b (mk_q_eq (vbvar 0) (vfvar x)))
    (tret (vfvar x)) m Hwf Hctx) as Hstatic.
  pose proof (ty_denote_gas_zero_tret_of_static_guard _ _ _ _ Hstatic) as Hzero.
  pose proof (ty_denote_gas_zero_inter_l _ _ _ _ _ Hzero) as Hleft.
  pose proof (ty_denote_gas_zero_inter_r _ _ _ _ _ Hzero) as Hright.
  change (m ⊨ FAnd
    (ty_guard_formula
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (precise_ty b (mk_q_eq (vbvar 0) (vfvar x))) (tret (vfvar x)))
      (precise_ty b (mk_q_eq (vbvar 0) (vfvar x))) (tret (vfvar x)))
    (FAnd
      (ty_denote_gas 1 (atom_env_to_lty_env (erase_ctx Γ))
        (CTOver b (mk_q_eq (vbvar 0) (vfvar x))) (tret (vfvar x)))
      (ty_denote_gas 1 (atom_env_to_lty_env (erase_ctx Γ))
        (CTUnder b (mk_q_eq (vbvar 0) (vfvar x))) (tret (vfvar x))))).
  apply res_models_and_iff. split.
  - eapply ty_denote_gas_guard_of_zero. exact Hzero.
  - apply res_models_and_iff. split.
    + apply var_over_denotation_gas. exact Hleft.
    + apply var_under_denotation_gas. exact Hright.
Qed.

(** A convenient derived form with ordinary environment lookup premises. *)
Lemma typing_var_self Φ Σ Γ b x :
  wf_ctx_under Σ Γ ->
  erase_ctx Γ !! x = Some (TBase b) ->
  has_context_type Φ Σ Γ (tret (vfvar x))
    (precise_ty b (mk_q_eq (vbvar 0) (vfvar x))).
Proof.
  intros Hctx Hlookup. apply CT_VarSelf.
  split; [exact Hctx|]. split.
  - assert (Hx : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    cbn [precise_ty over_ty under_ty wf_context_ty_at mk_q_eq qual_vars
      qual_lvars lvar_value_keys erase_ty].
    unfold lvars_wf_at. repeat split; try reflexivity.
    all: intros [k|z] Hz; cbn [lvar_wf_at] in *; set_solver by lia.
  - apply TT_Ret, VT_FVar. exact Hlookup.
Qed.
