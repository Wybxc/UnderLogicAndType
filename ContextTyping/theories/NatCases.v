(** Natural-input classification for genuine context-typing derivations. *)
From CoreLang Require Import Sugar BasicTypingProps StrongNormalization.
From ContextAlgebra Require Import ResourceInterfaceFacts.
From Denotation Require Import Context ConstDenote ConstDenoteBase
  TypeEquiv TypeEquivCore TypeEquivTermBase TypeEquivBody.
From ContextTyping Require Import Typing TypingRegular SoundnessVar SoundnessLam.

Definition nat_over_ty : context_ty := over_ty TNat qual_top.
Definition nat_singleton_ty (n : nat) : context_ty := const_precise_ty (cnat n).

Lemma nat_singleton_wf d D n : wf_context_ty_at d D (nat_singleton_ty n).
Proof.
  cbn [nat_singleton_ty const_precise_ty precise_ty over_ty under_ty
    wf_context_ty_at mk_q_eq qual_vars lvar_value_keys erase_ty].
  unfold lvars_wf_at. repeat split; try reflexivity.
  all: intros [k|x] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.

Lemma nat_over_wf d D : wf_context_ty_at d D nat_over_ty.
Proof.
  cbn [nat_over_ty over_ty wf_context_ty_at qual_top_on qual_vars qual_lvars].
  unfold lvars_wf_at. intros v H. apply elem_of_singleton in H as ->.
  cbn [lvar_wf_at]. lia.
Qed.

Lemma constant_precise_denotation gas Δ c (m : WfWorldT) :
  m ⊨ ty_denote_gas gas (atom_env_to_lty_env Δ)
    (const_precise_ty c) (tret (vconst c)).
Proof.
  assert (Hempty : m ⊨ ctx_denote_under ∅ CtxEmpty).
  { cbn [ctx_denote_under ctx_fv erase_ctx].
    rewrite storeA_restrict_empty_set.
    apply res_models_and_iff. split.
    - apply basic_world_formula_empty.
    - apply res_models_true. }
  pose proof (const_direct_denotation_gas_in_ctx gas ∅ c m Hempty
    ltac:(apply TT_Ret, VT_Const)) as Hden.
  eapply res_models_ty_denote_gas_env_agree_on with
    (Σ1 := atom_env_to_lty_env (ctx_erasure_under ∅ CtxEmpty))
    (X := relevant_lvars (const_precise_ty c) (tret (vconst c)));
    [reflexivity| |exact Hden].
  change (relevant_env (atom_env_to_lty_env (ctx_erasure_under ∅ CtxEmpty))
    (const_precise_ty c) (tret (vconst c)) =
    relevant_env (atom_env_to_lty_env Δ)
      (const_precise_ty c) (tret (vconst c))).
  transitivity (∅ : lty_env).
  - apply relevant_env_const_precise_atom_env_empty.
  - symmetry. apply relevant_env_const_precise_atom_env_empty.
Qed.

Lemma instantiate_ret_nat_var σ x n :
  σ !! x = Some (vconst (cnat n)) ->
  lstore_instantiate_tm (lstore_lift_free σ) (tret (vfvar x)) =
    tret (vconst (cnat n)).
Proof.
  intros Hx.
  unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
  cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
  rewrite lstore_free_part_lift_free.
  change (tret (match σ !! x with Some v => v | None => vfvar x end) =
    tret (vconst (cnat n))).
  rewrite Hx. reflexivity.
Qed.

Lemma denote_nat_var_constant Σ Γ x n (m : WfWorldT) :
  context_typing_wf Σ Γ (tret (vfvar x)) (nat_singleton_ty n) ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (cnat n))) ->
  m ⊨ ty_denote_under Σ Γ (nat_singleton_ty n) (tret (vfvar x)).
Proof.
  intros Hwf Hctx Hlookup.
  assert (Heq : tm_equiv_on m (tret (vconst (cnat n))) (tret (vfvar x))).
  { intros σ v Hσ. unfold tm_eval_in_store, expr_eval_in_store.
    rewrite (instantiate_ret_nat_var σ x n (Hlookup σ Hσ)). reflexivity. }
  assert (Htotal : tm_total_equiv_on m (tret (vconst (cnat n))) (tret (vfvar x))).
  { intros σ Hσ. rewrite (instantiate_ret_nat_var σ x n (Hlookup σ Hσ)).
    reflexivity. }
  pose proof (constant_precise_denotation (cty_depth (nat_singleton_ty n))
    (erase_ctx Γ) (cnat n) m) as Hconst.
  unfold ty_denote_under, ty_denote.
  eapply ty_denote_gas_tm_equiv; [|exact Hconst].
  split; [exact Heq|]. split; [exact Htotal|]. split.
  - apply ty_denote_gas_zero_of_guard. eapply ty_denote_gas_guard; exact Hconst.
  - eapply ty_denote_gas_zero_tret_of_static_guard.
    eapply context_typing_wf_denot_static_guard_full; eauto.
Qed.

Lemma ctx_denote_closed_bind Σ x τ :
  fv_cty τ = ∅ ->
  ctx_denote_under Σ (CtxBind x τ) =
    FAnd (basic_world_formula (atom_env_to_lty_env ({[x := erase_ty τ]})))
      (ty_denote ({[x := erase_ty τ]}) τ (tret (vfvar x))).
Proof.
  intros Hfv. cbn [ctx_denote_under ctx_fv erase_ctx].
  rewrite Hfv, storeA_restrict_empty_set.
  unfold store_union, store_insert, store_empty.
  rewrite map_empty_union. reflexivity.
Qed.

Lemma nat_over_fv : fv_cty nat_over_ty = ∅.
Proof.
  pose proof (wf_context_ty_at_fv_subset 0 ∅ nat_over_ty (nat_over_wf 0 ∅)) as H.
  apply leibniz_equiv. set_solver.
Qed.
Lemma nat_singleton_fv n : fv_cty (nat_singleton_ty n) = ∅.
Proof.
  pose proof (wf_context_ty_at_fv_subset 0 ∅ (nat_singleton_ty n)
    (nat_singleton_wf 0 ∅ n)) as H.
  apply leibniz_equiv. set_solver.
Qed.

Lemma nat_input_fiber_constant_on x X σ (m mfib : WfWorldT) :
  x ∈ X ->
  m ⊨ ctx_denote_under ∅ (CtxBind x nat_over_ty) ->
  res_fiber_from_projection m X σ mfib ->
  exists n, mfib ⊨ ctx_denote_under ∅ (CtxBind x (nat_singleton_ty n)).
Proof.
  intros HxX Hctx Hfib.
  rewrite ctx_denote_closed_bind in Hctx by apply nat_over_fv.
  apply res_models_and_iff in Hctx as [Hworld Hden].
  destruct (world_wf mfib) as [[s Hs] _].
  assert (Hsm : (m : WorldT) s).
  { eapply res_fiber_from_projection_store_source; eauto. }
  destruct (ty_denote_ret_fvar_base_const 1
    (atom_env_to_lty_env ({[x := TBase TNat]})) nat_over_ty TNat x m
    eq_refl Hden s Hsm) as [c [Hx Hc]].
  destruct c as [|b|n|tr|xs|z]; cbn [base_ty_of_const] in Hc; try discriminate.
  exists n.
  assert (Hlookup : forall s', (mfib : WorldT) s' ->
      s' !! x = Some (vconst (cnat n))).
  { intros s' Hs'.
    pose proof (res_fiber_from_projection_store_restrict_input
      m mfib X σ s Hfib Hs) as Hsproj.
    pose proof (res_fiber_from_projection_store_restrict_input
      m mfib X σ s' Hfib Hs') as Hs'proj.
    assert (Heq : store_restrict s X = store_restrict s' X) by congruence.
    assert (Hr : (storeA_restrict s X : gmap atom value) !! x =
      Some (vconst (cnat n))).
    { apply storeA_restrict_lookup_some_2; [exact Hx|set_solver]. }
    change ((store_restrict s X : gmap atom value) !! x =
      Some (vconst (cnat n))) in Hr.
    rewrite Heq in Hr.
    exact (proj2 (storeA_restrict_lookup_some s' X x _ Hr)). }
  assert (Hworld_fib : mfib ⊨ basic_world_formula
      (atom_env_to_lty_env ({[x := TBase TNat]}))).
  { eapply basic_world_formula_res_subset; [|exact Hworld].
    eapply res_subset_fiber_source; eauto. }
  assert (Hden_fib : mfib ⊨ ty_denote ({[x := TBase TNat]})
      nat_over_ty (tret (vfvar x))).
  { eapply ty_denote_gas_over_ret_fvar_fiber_stable_any; eauto.
    - apply atom_store_to_lvar_store_closed.
    - unfold qual_dom. cbn [qual_top_on qual_lvars].
      rewrite lvars_fv_singleton_bound. set_solver. }
  assert (Hctx_fib : mfib ⊨ ctx_denote_under ∅ (CtxBind x nat_over_ty)).
  { rewrite ctx_denote_closed_bind by apply nat_over_fv.
    apply res_models_and_iff. split; assumption. }
  rewrite ctx_denote_closed_bind by apply nat_singleton_fv.
  apply res_models_and_iff. split; [exact Hworld_fib|].
  eapply (denote_nat_var_constant ∅ (CtxBind x nat_over_ty)); eauto.
  split.
  - apply basic_ctx_bind; [set_solver|apply nat_over_wf].
  - split; [apply nat_singleton_wf|].
    apply TT_Ret, VT_FVar. apply lookup_singleton_eq.
Qed.

Lemma const_precise_wf d D c : wf_context_ty_at d D (const_precise_ty c).
Proof.
  cbn [const_precise_ty precise_ty over_ty under_ty wf_context_ty_at
    mk_q_eq qual_vars lvar_value_keys erase_ty].
  unfold lvars_wf_at. repeat split; try reflexivity.
  all: intros [k|x] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.

Lemma typing_const_in_ctx Φ Σ Γ c :
  context_typing_wf Σ Γ (tret (vconst c)) (const_precise_ty c) ->
  has_context_type Φ Σ Γ (tret (vconst c)) (const_precise_ty c).
Proof.
  intros Hwf. eapply CT_CtxSub with (Γ2 := CtxEmpty); [exact Hwf| |].
  - apply CT_Const. split; [constructor|]. split;
      [apply const_precise_wf|apply TT_Ret, VT_Const].
  - split; [exact (proj1 Hwf)|]. split; [constructor|]. split.
    + intros x Hx. cbn [fv_tm fv_value] in Hx.
      pose proof (wf_context_ty_at_fv_subset 0 ∅ (const_precise_ty c)
        (const_precise_wf 0 ∅ c)) as Hfv. set_solver.
    + intros m _. exists m. split; [apply res_restrict_le|].
      cbn [ctx_denote_under ctx_fv erase_ctx].
      rewrite storeA_restrict_empty_set.
      apply res_models_and_iff. split;
        [apply basic_world_formula_empty|apply res_models_true].
Qed.

Definition nat_pair_ctx x y τx τy : ctx :=
  CtxComma (CtxComma CtxEmpty (CtxBind x τx)) (CtxBind y τy).

Lemma ctx_denote_closed_env Σ Γ :
  ctx_fv Γ = ∅ -> ctx_denote_under Σ Γ = ctx_denote_under ∅ Γ.
Proof.
  intros H. rewrite (ctx_denote_under_minimal Σ Γ), H,
    storeA_restrict_empty_set. reflexivity.
Qed.

Lemma nat_pair_ctx_wf x y τx τy :
  x <> y -> basic_context_ty ∅ τx -> basic_context_ty ∅ τy ->
  wf_ctx_under ∅ (nat_pair_ctx x y τx τy).
Proof.
  intros Hxy Hx Hy. unfold wf_ctx_under, nat_pair_ctx.
  cbn [basic_ctx ctx_dom]. repeat split; try set_solver.
  eapply wf_context_ty_at_mono_env; [|exact Hy]. set_solver.
Qed.

Lemma nat_pair_denote_inv Σ x y τx τy (m : WfWorldT) :
  fv_cty τx = ∅ -> fv_cty τy = ∅ ->
  m ⊨ ctx_denote_under Σ (nat_pair_ctx x y τx τy) ->
  m ⊨ ctx_denote_under ∅ (CtxBind x τx) /\
  m ⊨ ctx_denote_under ∅ (CtxBind y τy).
Proof.
  intros Hx Hy H.
  unfold nat_pair_ctx in H.
  apply res_models_and_iff in H as [_ H].
  apply res_models_and_iff in H as [Hleft Hright].
  apply res_models_and_iff in Hleft as [_ Hleft].
  apply res_models_and_iff in Hleft as [_ Hleft].
  split.
  - rewrite ctx_denote_closed_bind by exact Hx.
    cbn [ctx_fv] in Hleft. rewrite Hx, storeA_restrict_empty_set in Hleft.
    unfold store_union, store_empty in Hleft. rewrite map_empty_union in Hleft.
    exact Hleft.
  - rewrite ctx_denote_closed_bind by exact Hy.
    cbn [ctx_fv] in Hright. rewrite Hy, storeA_restrict_empty_set in Hright.
    unfold store_union, store_empty in Hright. rewrite map_empty_union in Hright.
    exact Hright.

Qed.

Lemma nat_pair_denote_intro x y τx τy (m : WfWorldT) :
  basic_context_ty ∅ τx ->
  fv_cty τx = ∅ -> fv_cty τy = ∅ ->
  m ⊨ ctx_denote_under ∅ (CtxBind x τx) ->
  m ⊨ ctx_denote_under ∅ (CtxBind y τy) ->
  m ⊨ ctx_denote_under ∅ (nat_pair_ctx x y τx τy).
Proof.
  intros Hτx Hx Hy Hdx Hdy. unfold nat_pair_ctx.
  apply ctx_denote_under_comma_intro.
  - cbn [basic_ctx ctx_dom]. repeat split; try set_solver.
  - apply ctx_denote_under_comma_intro; [constructor| |].
    + cbn [ctx_denote_under ctx_fv erase_ctx].
      rewrite storeA_restrict_empty_set.
      apply res_models_and_iff. split;
        [apply basic_world_formula_empty|apply res_models_true].
    + rewrite ctx_denote_closed_env; [exact Hdx|exact Hx].
  - rewrite ctx_denote_closed_env; [exact Hdy|exact Hy].
Qed.

Lemma nat_pair_fiber_constants x y σ (m mfib : WfWorldT) :
  m ⊨ ctx_denote_under ∅ (nat_pair_ctx x y nat_over_ty nat_over_ty) ->
  res_fiber_from_projection m {[x;y]} σ mfib ->
  exists n k, mfib ⊨ ctx_denote_under ∅
    (nat_pair_ctx x y (nat_singleton_ty n) (nat_singleton_ty k)).
Proof.
  intros Hctx Hfib.
  destruct (nat_pair_denote_inv ∅ x y nat_over_ty nat_over_ty m
    nat_over_fv nat_over_fv Hctx) as [Hx Hy].
  destruct (nat_input_fiber_constant_on x {[x;y]} σ m mfib
    ltac:(set_solver) Hx Hfib) as [n Hn].
  destruct (nat_input_fiber_constant_on y {[x;y]} σ m mfib
    ltac:(set_solver) Hy Hfib) as [k Hk].
  exists n,k. apply nat_pair_denote_intro; try assumption;
    [apply nat_singleton_wf|apply nat_singleton_fv|apply nat_singleton_fv].
Qed.
