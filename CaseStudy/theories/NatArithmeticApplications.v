(** Apply the proved arithmetic library inside arbitrary dependent contexts.
    The context transport reconstructs only closed Over-top bindings. *)
From CaseStudy Require Import NatArithmetic NatArithmeticTyping NatArithmeticStages.
From Denotation Require Import Context TypeEquivTermBase.
From ContextTyping Require Import Typing NatCases BasicBindings Subtyping TypingRegular.
From CoreLang Require Import Sugar BasicTypingProps.

Lemma nat_pair_over_ctx_sub Γ x y X :
  wf_ctx_under ∅ Γ -> x <> y ->
  erase_ctx Γ !! x = Some (TBase TNat) ->
  erase_ctx Γ !! y = Some (TBase TNat) -> X ⊆ ({[x;y]} : aset) ->
  ctx_sub_under ∅ X Γ (nat_pair_ctx x y nat_over_ty nat_over_ty).
Proof.
  intros HΓ Hxy Hx Hy HX.
  destruct (nat_pair_lookups x y nat_over_ty nat_over_ty Hxy eq_refl eq_refl)
    as [Hxp Hyp].
  split; [exact HΓ|]. split.
  - apply nat_pair_ctx_wf; [exact Hxy|apply nat_over_wf|apply nat_over_wf].
  - split.
    + intros z Hz. assert (Hz' : z=x \/ z=y) by set_solver.
      destruct Hz' as [-> | ->]; transitivity (Some (TBase TNat));
        first [exact Hx|exact Hy|symmetry; exact Hxp|symmetry; exact Hyp].
    + intros m Hctx. exists m. split; [apply res_restrict_le|].
      apply nat_pair_denote_intro; [apply nat_over_wf|apply nat_over_fv|apply nat_over_fv| |];
        eapply ctx_denote_under_over_top_binding; eassumption.
Qed.

Lemma arithmetic_body_context_typed Φ Γ is_add x y :
  wf_ctx_under ∅ Γ -> x <> y ->
  erase_ctx Γ !! x = Some (TBase TNat) ->
  erase_ctx Γ !! y = Some (TBase TNat) ->
  has_context_type Φ ∅ Γ (arithmetic_body is_add (vfvar x) (vfvar y))
    (nat_graph_ty (arithmetic_function is_add) x y).
Proof.
  intros HΓ Hxy Hx Hy.
  pose proof (arithmetic_body_typing Φ is_add x y Hxy) as Hsource.
  eapply CT_CtxSub; [|exact Hsource|].
  - split; [exact HΓ|]. split.
    + apply nat_graph_wf; apply elem_of_dom; eauto.
    + apply arithmetic_body_typed; assumption.
  - apply nat_pair_over_ctx_sub; try assumption.
    pose proof (typing_wf_under _ _ _ _ _ Hsource) as Hwf.
    pose proof (context_typing_wf_fv_tm_subset _ _ _ _ Hwf) as HeFV.
    pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf) as HτFV.
    cbn [nat_pair_ctx erase_ctx] in HeFV, HτFV.
    unfold store_union, store_empty in HeFV, HτFV.
    rewrite !map_empty_union, !dom_union_L in HeFV, HτFV.
    setoid_rewrite (dom_singleton_L (M:=gmap atom) (D:=aset)) in HeFV.
    setoid_rewrite (dom_singleton_L (M:=gmap atom) (D:=aset)) in HτFV.
    set_solver.
Qed.

Lemma arithmetic_app2_basic is_add Δ x y :
  Δ !! x = Some (TBase TNat) -> Δ !! y = Some (TBase TNat) ->
  tm_has_type Δ
    (NatArithmetic.app2 (arithmetic_value is_add) (vfvar x) (vfvar y)) (TBase TNat).
Proof.
  intros Hx Hy. unfold NatArithmetic.app2.
  eapply basic_typing_tapp_tm; [|apply VT_FVar; exact Hy].
  eapply TT_App; [apply arithmetic_value_typed|apply VT_FVar; exact Hx].
Qed.

Lemma arithmetic_app2_instantiate is_add σ x y n k :
  σ !! x = Some (vnat n) -> σ !! y = Some (vnat k) ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (NatArithmetic.app2 (arithmetic_value is_add) (vfvar x) (vfvar y)) =
  NatArithmetic.app2 (arithmetic_value is_add) (vnat n) (vnat k).
Proof.
  intros Hx Hy. destruct is_add; arithmetic_instantiate;
    setoid_rewrite Hx; setoid_rewrite Hy; vm_compute; reflexivity.
Qed.

Lemma arithmetic_app2_context_typed Φ Γ is_add x y :
  wf_ctx_under ∅ Γ -> x <> y ->
  erase_ctx Γ !! x = Some (TBase TNat) ->
  erase_ctx Γ !! y = Some (TBase TNat) ->
  has_context_type Φ ∅ Γ
    (NatArithmetic.app2 (arithmetic_value is_add) (vfvar x) (vfvar y))
    (nat_graph_ty (arithmetic_function is_add) x y).
Proof.
  intros HΓ Hxy Hx Hy. eapply CT_Conv.
  - split; [exact HΓ|]. split.
    + apply nat_graph_wf; apply elem_of_dom; eauto.
    + apply arithmetic_app2_basic; assumption.
  - apply arithmetic_body_context_typed; assumption.
  - intros m Hctx.
    assert (Hargs : forall σ, (m : WorldT) σ -> exists n k,
      σ !! x = Some (vnat n) /\ σ !! y = Some (vnat k)).
    { intros σ Hσ.
      destruct (ctx_denote_under_lookup_typed ∅ Γ x _ m σ HΓ Hx Hctx Hσ)
        as [vx [Hvx Htx]].
      destruct (ctx_denote_under_lookup_typed ∅ Γ y _ m σ HΓ Hy Hctx Hσ)
        as [vy [Hvy Hty]].
      destruct (basic_typing_nat_canonical_form vx Htx) as [n ->].
      destruct (basic_typing_nat_canonical_form vy Hty) as [k ->].
      exists n,k. auto. }
    split.
    + intros σ v Hσ. destruct (Hargs σ Hσ) as [n [k [Hn Hk]]].
      unfold tm_eval_in_store, expr_eval_in_store.
      rewrite (arithmetic_body_instantiate is_add σ x y n k Hn Hk),
        (arithmetic_app2_instantiate is_add σ x y n k Hn Hk).
      symmetry. exact (proj1 (arithmetic_prefix_equivalence _ _
        (arithmetic_body_prefix is_add n k)) v).
    + intros σ Hσ. destruct (Hargs σ Hσ) as [n [k [Hn Hk]]].
      rewrite (arithmetic_body_instantiate is_add σ x y n k Hn Hk),
        (arithmetic_app2_instantiate is_add σ x y n k Hn Hk).
      symmetry. exact (proj2 (arithmetic_prefix_equivalence _ _
        (arithmetic_body_prefix is_add n k))).
Qed.

Lemma arithmetic_app2_over_context_typed Φ Γ is_add x y :
  wf_ctx_under ∅ Γ -> x <> y ->
  erase_ctx Γ !! x = Some (TBase TNat) ->
  erase_ctx Γ !! y = Some (TBase TNat) ->
  has_context_type Φ ∅ Γ
    (NatArithmetic.app2 (arithmetic_value is_add) (vfvar x) (vfvar y))
    (CTOver TNat (q_nat_graph (arithmetic_function is_add)
      (LVFree x) (LVFree y) (LVBound 0))).
Proof.
  intros HΓ Hxy Hx Hy.
  apply typing_inter_l with (τ2 := CTUnder TNat
    (q_nat_graph (arithmetic_function is_add) (LVFree x) (LVFree y) (LVBound 0))).
  exact (arithmetic_app2_context_typed Φ Γ is_add x y HΓ Hxy Hx Hy).
Qed.
