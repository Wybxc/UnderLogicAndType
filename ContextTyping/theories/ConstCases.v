(** Precise constants in nonempty constant fibers, for every base type. *)
From Denotation Require Import Context ConstDenote ConstDenoteBase TypeEquiv TypeEquivCore
  TypeEquivTermBase ResultQualifier.
From ContextTyping Require Import Typing TypingRegular NatCases SoundnessLam BasicBindings.

Lemma const_precise_fv c : fv_cty (const_precise_ty c) = ∅.
Proof.
  pose proof (basic_context_ty_fv_subset ∅ _ (const_precise_wf 0 ∅ c)). set_solver.
Qed.

Lemma instantiate_ret_const_var σ x c :
  σ !! x = Some (vconst c) ->
  lstore_instantiate_tm (lstore_lift_free σ) (tret (vfvar x)) = tret (vconst c).
Proof.
  intros Hx. unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
  cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
  rewrite lstore_free_part_lift_free.
  change (tret (match σ !! x with Some v => v | None => vfvar x end) = tret (vconst c)).
  rewrite Hx. reflexivity.
Qed.

Lemma denote_const_var_constant Σ Γ x c (m : WfWorldT) :
  context_typing_wf Σ Γ (tret (vfvar x)) (const_precise_ty c) ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst c)) ->
  m ⊨ ty_denote_under Σ Γ (const_precise_ty c) (tret (vfvar x)).
Proof.
  intros Hwf Hctx Hlookup.
  assert (Heq : tm_equiv_on m (tret (vconst c)) (tret (vfvar x))).
  { intros σ v Hσ. unfold tm_eval_in_store, expr_eval_in_store.
    rewrite (instantiate_ret_const_var σ x c (Hlookup σ Hσ)). reflexivity. }
  assert (Htotal : tm_total_equiv_on m (tret (vconst c)) (tret (vfvar x))).
  { intros σ Hσ. rewrite (instantiate_ret_const_var σ x c (Hlookup σ Hσ)). reflexivity. }
  pose proof (constant_precise_denotation (cty_depth (const_precise_ty c))
    (erase_ctx Γ) c m) as Hconst.
  unfold ty_denote_under, ty_denote.
  eapply ty_denote_gas_tm_equiv; [|exact Hconst].
  split; [exact Heq|]. split; [exact Htotal|]. split.
  - apply ty_denote_gas_zero_of_guard. eapply ty_denote_gas_guard; exact Hconst.
  - eapply ty_denote_gas_zero_tret_of_static_guard.
    eapply context_typing_wf_denot_static_guard_full; eauto.
Qed.

Lemma const_var_denote_from_basic_world x c (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=TBase (base_ty_of_const c)]}) ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst c)) ->
  m ⊨ ty_denote {[x:=TBase (base_ty_of_const c)]}
    (const_precise_ty c) (tret (vfvar x)).
Proof.
  intros Hworld Hlookup.
  assert (Hstatic : m ⊨ ty_static_guard_formula
      (atom_env_to_lty_env {[x:=TBase (base_ty_of_const c)]})
      (const_precise_ty c) (tret (vfvar x))).
  { pose proof Hworld as Hworld'.
    apply basic_world_formula_models_iff in Hworld' as [Hlc [Hscope Htyped]].
    unfold ty_static_guard_formula. apply res_models_and_iff. split.
    - apply context_ty_wf_formula_models_iff.
      split; [exact Hlc|]. split; [exact Hscope|].
      rewrite atom_store_to_lvar_store_dom. apply basic_context_ty_to_lvars.
      apply const_precise_wf.
    - apply res_models_and_iff. split; [exact Hworld|].
      apply expr_basic_typing_formula_models_iff.
      split; [exact Hlc|]. split; [exact Hscope|].
      apply basic_tm_has_ltype_of_atom_typing.
      + apply atom_store_to_lvar_store_closed.
      + rewrite lvar_store_to_atom_store_atom_store. apply TT_Ret, VT_FVar.
        apply map_lookup_singleton. }
  pose proof (constant_precise_denotation (cty_depth (const_precise_ty c))
    ({[x:=TBase (base_ty_of_const c)]} : gmap atom ty) c m) as Hconst.
  unfold ty_denote. eapply ty_denote_gas_tm_equiv; [|exact Hconst].
  split.
  - intros σ v Hσ. unfold tm_eval_in_store, expr_eval_in_store.
    rewrite (instantiate_ret_const_var σ x c (Hlookup σ Hσ)). reflexivity.
  - split.
    + intros σ Hσ. rewrite (instantiate_ret_const_var σ x c (Hlookup σ Hσ)). reflexivity.
    + split.
      * apply ty_denote_gas_zero_of_guard. eapply ty_denote_gas_guard; exact Hconst.
      * apply ty_denote_gas_zero_tret_of_static_guard. exact Hstatic.
Qed.

Lemma const_bind_denote_from_basic_world x c (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=TBase (base_ty_of_const c)]}) ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst c)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind x (const_precise_ty c)).
Proof.
  intros Hworld Hlookup.
  rewrite ctx_denote_closed_bind.
  - apply res_models_and_iff. split; [exact Hworld|].
    apply const_var_denote_from_basic_world; assumption.
  - pose proof (basic_context_ty_fv_subset ∅ _ (const_precise_wf 0 ∅ c)). set_solver.
Qed.

Lemma fiber_store_lookup_eq (m mfib : WfWorldT) X σ x s t :
  x ∈ X -> res_fiber_from_projection m X σ mfib ->
  (mfib : WorldT) s -> (mfib : WorldT) t -> s !! x = t !! x.
Proof.
  intros Hx Hfib Hs Ht.
  pose proof (res_fiber_from_projection_store_restrict_input m mfib X σ s Hfib Hs) as HsX.
  pose proof (res_fiber_from_projection_store_restrict_input m mfib X σ t Hfib Ht) as HtX.
  pose proof (f_equal (fun ρ : StoreT => ρ !! x) (eq_trans HsX (eq_sym HtX))) as Heq.
  exact (eq_trans (eq_sym (store_restrict_lookup_at s X x Hx))
    (eq_trans Heq (store_restrict_lookup_at t X x Hx))).
Qed.

Lemma const_bind_denote_fiber x c (m mfib : WfWorldT) X σ s :
  x ∈ X ->
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=TBase (base_ty_of_const c)]}) ->
  res_fiber_from_projection m X σ mfib ->
  (mfib : WorldT) s -> s !! x = Some (vconst c) ->
  mfib ⊨ ctx_denote_under ∅ (CtxBind x (const_precise_ty c)).
Proof.
  intros Hx Hworld Hfib Hs Hsx. apply const_bind_denote_from_basic_world.
  - eapply basic_world_formula_res_subset; [|exact Hworld].
    eapply res_subset_fiber_source; exact Hfib.
  - intros t Ht. exact (eq_trans (fiber_store_lookup_eq m mfib X σ x t s Hx Hfib Ht Hs) Hsx).
Qed.

Lemma ctx_const_bind_denote_fiber Σ Γ x c (m mfib : WfWorldT) X σ s :
  wf_ctx_under Σ Γ -> erase_ctx Γ !! x = Some (TBase (base_ty_of_const c)) ->
  m ⊨ ctx_denote_under Σ Γ -> x ∈ X ->
  res_fiber_from_projection m X σ mfib ->
  (mfib : WorldT) s -> s !! x = Some (vconst c) ->
  mfib ⊨ ctx_denote_under ∅ (CtxBind x (const_precise_ty c)).
Proof.
  intros HΓ Hx Hctx HX Hfib Hs Hsx.
  eapply const_bind_denote_fiber;
    [exact HX| |exact Hfib|exact Hs|exact Hsx].
  exact (ctx_denote_under_basic_singleton Σ Γ x _ m HΓ Hx Hctx).
Qed.

Lemma const_precise_bind_lookup x c (m : WfWorldT) :
  m ⊨ ctx_denote_under ∅ (CtxBind x (const_precise_ty c)) ->
  forall σ, (m : WorldT) σ -> σ !! x = Some (vconst c).
Proof.
  intros Hctx σ Hσ. rewrite ctx_denote_closed_bind in Hctx.
  - apply res_models_and_iff in Hctx as [_ Hden].
    change (m ⊨ ty_denote_gas 2
      (atom_env_to_lty_env {[x:=TBase (base_ty_of_const c)]})
      (const_precise_ty c) (tret (vfvar x))) in Hden.
    apply res_models_and_iff in Hden as [_ Hden].
    apply res_models_and_iff in Hden as [Hover _].
    eapply (ty_denote_over_ret_fvar_const_lookup 0 _ x c m σ);
      [apply atom_store_to_lvar_store_closed|exact Hover|exact Hσ].
  - pose proof (basic_context_ty_fv_subset ∅ _ (const_precise_wf 0 ∅ c)). set_solver.
Qed.
