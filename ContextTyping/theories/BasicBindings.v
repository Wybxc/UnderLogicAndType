(** Closed Over-top bindings can be reconstructed from basic typing.
    No refinement or ordinary-arrow stability is assumed. *)
From Denotation Require Import Context TypeEquiv TypeEquivCore.
From ContextTyping Require Import Typing NatCases PrimOpConcreteContext TypingRegular.

Lemma ctx_denote_under_basic_singleton Σ Γ x T (m : WfWorldT) :
  wf_ctx_under Σ Γ -> erase_ctx Γ !! x = Some T ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=T]}).
Proof.
  intros HΓ Hx Hctx.
  eapply basic_world_formula_subenv; [|exact (ctx_denote_under_basic_world Σ Γ m Hctx)].
  intros [i|z] U Hz.
  - rewrite atom_store_to_lvar_store_lookup_bound_none in Hz. discriminate.
  - rewrite atom_store_to_lvar_store_lookup_free in Hz |- *.
    change (({[x:=T]} : gmap atom ty) !! z = Some U) in Hz.
    destruct (decide (z=x)) as [->|Hne].
    + assert (HT : U = T).
      { assert (Heq : Some U = Some T).
        { transitivity (({[x:=T]} : gmap atom ty) !! x);
            [symmetry; exact Hz|apply map_lookup_singleton]. }
        now inversion Heq. }
      subst U.
      transitivity (erase_ctx Γ !! x); [symmetry|exact Hx].
      apply erase_ctx_lookup_ctx_erasure_under_of_basic_ctx; [exact HΓ|].
      apply elem_of_dom; eauto.
    + assert (Heq : Some U = None).
      { transitivity (({[x:=T]} : gmap atom ty) !! z);
          [symmetry; exact Hz|apply map_lookup_singleton_ne; exact Hne]. }
      discriminate.
Qed.

Lemma ctx_denote_under_lookup_typed Σ Γ x T (m : WfWorldT) σ :
  wf_ctx_under Σ Γ -> erase_ctx Γ !! x = Some T ->
  m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
  exists v, σ !! x = Some v /\ value_has_type ∅ v T.
Proof.
  intros HΓ Hx Hctx Hσ.
  pose proof (ctx_denote_under_basic_singleton Σ Γ x T m HΓ Hx Hctx) as Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope [_ Hstores]]].
  assert (Hxd : x ∈ world_dom (m : WorldT)).
  { apply Hscope. rewrite lvars_fv_atom_env_to_lty_env_dom.
    apply elem_of_dom. exists T. apply map_lookup_singleton. }
  assert (Hxdσ : x ∈ dom (σ : gmap atom value)).
  { rewrite (wfworld_store_dom m σ Hσ). exact Hxd. }
  apply elem_of_dom in Hxdσ as [v Hv]. exists v. split; [exact Hv|].
  pose proof (Hstores (lstore_lift_free σ)
    ltac:(exists σ; split; [exact Hσ|reflexivity])) as Hstore.
  apply (Hstore (LVFree x) T v).
  - rewrite atom_store_to_lvar_store_lookup_free. apply map_lookup_singleton.
  - rewrite lstore_lift_free_lookup_free. exact Hv.
Qed.

Lemma over_top_bind_denote_from_basic_world x b (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=TBase b]}) ->
  m ⊨ ctx_denote_under ∅ (CtxBind x (CTOver b qual_top)).
Proof.
  intros Hworld.
  assert (Hclosed : fv_cty (CTOver b qual_top) = ∅).
  { pose proof (basic_context_ty_fv_subset ∅ _ (over_top_basic b)). set_solver. }
  rewrite ctx_denote_closed_bind by exact Hclosed.
  apply res_models_and_iff. split; [exact Hworld|].
  apply ty_denote_gas_over_top_from_zero.
  apply ty_denote_gas_zero_tret_of_static_guard.
  pose proof Hworld as Hparts.
  apply basic_world_formula_models_iff in Hparts as [Hlc [Hscope Htyped]].
  unfold ty_static_guard_formula. apply res_models_and_iff. split.
  - apply context_ty_wf_formula_models_iff.
    split; [exact Hlc|]. split; [exact Hscope|].
    rewrite atom_store_to_lvar_store_dom.
    apply basic_context_ty_to_lvars.
    eapply wf_context_ty_at_mono_env; [|exact (over_top_basic b)]. set_solver.
  - apply res_models_and_iff. split; [exact Hworld|].
    apply expr_basic_typing_formula_models_iff.
    split; [exact Hlc|]. split; [exact Hscope|].
    apply basic_tm_has_ltype_of_atom_typing.
    + apply atom_store_to_lvar_store_closed.
    + rewrite lvar_store_to_atom_store_atom_store. apply TT_Ret, VT_FVar.
      apply map_lookup_singleton.
Qed.

Lemma ctx_denote_under_over_top_binding Σ Γ x b (m : WfWorldT) :
  wf_ctx_under Σ Γ -> erase_ctx Γ !! x = Some (TBase b) ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ctx_denote_under ∅ (CtxBind x (CTOver b qual_top)).
Proof.
  intros HΓ Hx Hctx. apply over_top_bind_denote_from_basic_world.
  exact (ctx_denote_under_basic_singleton Σ Γ x (TBase b) m HΓ Hx Hctx).
Qed.

Lemma typing_over_top_var Φ Σ Γ x b :
  wf_ctx_under Σ Γ -> erase_ctx Γ !! x = Some (TBase b) ->
  has_context_type Φ Σ Γ (tret (vfvar x)) (CTOver b qual_top).
Proof.
  intros HΓ Hx.
  assert (Hdom : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hfresh : x ∉ dom Σ).
  { apply not_elem_of_dom. eapply basic_ctx_erase_dom_fresh_none; eassumption. }
  assert (Hclosed : fv_cty (CTOver b qual_top) = ∅).
  { pose proof (basic_context_ty_fv_subset ∅ _ (over_top_basic b)). set_solver. }
  assert (Hbind : wf_ctx_under Σ (CtxBind x (CTOver b qual_top))).
  { split; [set_solver|].
    eapply wf_context_ty_at_mono_env; [|exact (over_top_basic b)]. set_solver. }
  eapply CT_CtxSub with (Γ2 := CtxBind x (CTOver b qual_top)).
  - split; [exact HΓ|]. split.
    + eapply wf_context_ty_at_mono_env; [|exact (over_top_basic b)]. set_solver.
    + apply TT_Ret, VT_FVar. exact Hx.
  - apply CT_Var. split; [exact Hbind|]. split.
    + eapply wf_context_ty_at_mono_env; [|exact (over_top_basic b)]. set_solver.
    + apply TT_Ret, VT_FVar. apply map_lookup_singleton.
  - split; [exact HΓ|]. split; [exact Hbind|]. split.
    + intros z Hz. rewrite Hclosed in Hz.
      cbn [fv_tm fv_value] in Hz. assert (z=x) by set_solver. subst z.
      transitivity (Some (TBase b)); [exact Hx|symmetry; apply map_lookup_singleton].
    + intros m Hctx. exists m. split; [apply res_restrict_le|].
      rewrite ctx_denote_closed_env; [|exact Hclosed].
      exact (ctx_denote_under_over_top_binding Σ Γ x b m HΓ Hx Hctx).
Qed.

Lemma wf_ctx_comma_closed_bind Σ Γ x τ :
  wf_ctx_under Σ Γ -> x ∉ dom Σ ∪ ctx_dom Γ ->
  basic_context_ty ∅ τ -> wf_ctx_under Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros HΓ Hx Hτ. split; [exact HΓ|]. split.
  - split; [exact Hx|].
    eapply wf_context_ty_at_mono_env; [|exact Hτ]. set_solver.
  - cbn [ctx_dom]. set_solver.
Qed.

Lemma erase_ctx_comma_lookup_old Γ x τ z T :
  erase_ctx Γ !! z = Some T ->
  erase_ctx (CtxComma Γ (CtxBind x τ)) !! z = Some T.
Proof.
  intros Hz. cbn [erase_ctx]. apply map_lookup_union_Some_raw. left. exact Hz.
Qed.

Lemma erase_ctx_comma_lookup_new Γ x τ :
  x ∉ dom (erase_ctx Γ) ->
  erase_ctx (CtxComma Γ (CtxBind x τ)) !! x = Some (erase_ty τ).
Proof.
  intros Hx. cbn [erase_ctx]. apply map_lookup_union_Some_raw. right. split.
  - apply not_elem_of_dom. exact Hx.
  - apply map_lookup_singleton.
Qed.

Lemma erase_ctx_comma_lookup_new_wf Σ Γ x τ :
  wf_ctx_under Σ (CtxComma Γ (CtxBind x τ)) ->
  erase_ctx (CtxComma Γ (CtxBind x τ)) !! x = Some (erase_ty τ).
Proof.
  intros [HΓ [[Hx Hτ] Hdisj]]. apply erase_ctx_comma_lookup_new.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ HΓ) as Hdom.
  change (x ∉ dom (erase_ctx Γ : gmap atom ty)).
  setoid_rewrite Hdom. clear -Hx. set_solver.
Qed.

Lemma typing_var_right_wf Φ Γ x τ :
  wf_ctx_under ∅ (CtxComma Γ (CtxBind x τ)) ->
  has_context_type Φ ∅ (CtxComma Γ (CtxBind x τ)) (tret (vfvar x)) τ.
Proof.
  intros Hwf. apply CT_VarR. split; [exact Hwf|]. split.
  - destruct Hwf as [HΓ [[Hx Hτ] Hdisj]].
    eapply wf_context_ty_at_mono_env; [|exact Hτ].
    pose proof (basic_ctx_erase_dom (dom (∅ : gmap atom ty)) Γ HΓ) as HD.
    cbn [erase_ctx]. unfold store_union. rewrite dom_union_L.
    change (dom (∅ : gmap atom ty) ∪ ctx_dom Γ ⊆
      dom (erase_ctx Γ : gmap atom ty) ∪ dom ({[x:=erase_ty τ]} : gmap atom ty)).
    rewrite HD. clear; set_solver.
  - apply TT_Ret, VT_FVar.
    exact (erase_ctx_comma_lookup_new_wf ∅ Γ x τ Hwf).
Qed.
