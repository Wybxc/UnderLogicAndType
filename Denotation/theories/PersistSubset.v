(** A persistent binding survives a nonempty same-domain subworld because
    its entire relevant projection is a singleton.  No such statement is
    assumed for ordinary arrows or arbitrary under bindings. *)
From Denotation Require Import Context.

Lemma res_subset_singleton_projection (m n : WfWorldT) X (σ : StoreT) :
  res_subset n m ->
  res_restrict m X = (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  res_restrict n X = (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT).
Proof.
  intros [Hdom Hstores] Hsingle.
  change (world_dom (n : WorldT) = world_dom (m : WorldT)) in Hdom.
  apply wfworld_ext. apply world_ext.
  - rewrite res_restrict_dom, Hdom.
    pose proof (f_equal (fun w : WfWorldT => world_dom (w : WorldT)) Hsingle) as HD.
    change (world_dom (res_restrict m X : WorldT) = dom (σ : StoreT)) in HD.
    rewrite res_restrict_dom in HD. exact HD.
  - intros τ. change ((exists ρ, (n : WorldT) ρ /\ store_restrict ρ X = τ) <-> τ = σ).
    split.
    + intros [ρ [Hρ Hρτ]].
      exact (eq_trans (eq_sym Hρτ)
        (res_restrict_singleton_store_eq m X σ ρ Hsingle (Hstores ρ Hρ))).
    + intros ->. destruct (world_wf n) as [[ρ Hρ] _].
      exists ρ. split; [exact Hρ|].
      exact (res_restrict_singleton_store_eq m X σ ρ Hsingle (Hstores ρ Hρ)).
Qed.

Lemma ctx_bind_persist_res_subset Σ x τ (m n : WfWorldT) :
  basic_ctx (dom Σ) (CtxBind x (CTPersist τ)) ->
  m ⊨ ctx_denote_under Σ (CtxBind x (CTPersist τ)) ->
  res_subset n m ->
  n ⊨ ctx_denote_under Σ (CtxBind x (CTPersist τ)).
Proof.
  intros Hbasic Hctx Hsub.
  destruct (ctx_bind_persist_singleton_projection Σ x τ m Hbasic Hctx)
    as [σ [Hdom Hsingle]].
  pose proof (res_subset_singleton_projection m n _ σ Hsub Hsingle) as Hsingle_n.
  apply (proj2 (res_models_minimal_on (fv_cty τ ∪ {[x]}) n _
    (formula_fv_ctx_bind_persist_subset Σ x τ))).
  rewrite Hsingle_n, <- Hsingle.
  apply (proj1 (res_models_minimal_on (fv_cty τ ∪ {[x]}) m _
    (formula_fv_ctx_bind_persist_subset Σ x τ))). exact Hctx.
Qed.
