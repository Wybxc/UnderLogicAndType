(** Additive prefix weakening uses the same world, rather than dropping
    stores or assuming arbitrary refinement stability under subworlds. *)
From Denotation Require Import Context.
From ContextTyping Require Import Typing TypingRegular.

Lemma ctx_sub_comma_prefix Σ Γ Δ X :
  wf_ctx_under Σ (CtxComma Γ Δ) ->
  X ⊆ dom (erase_ctx Γ) ->
  ctx_sub_under Σ X (CtxComma Γ Δ) Γ.
Proof.
  intros Hwf HX.
  assert (HΓ : wf_ctx_under Σ Γ) by exact (proj1 Hwf).
  split; [exact Hwf|]. split; [exact HΓ|]. split.
  - unfold ty_env_agree_on. intros x Hx. cbn [erase_ctx].
    destruct (proj1 (elem_of_dom (erase_ctx Γ) x) (HX x Hx)) as [T HT].
    transitivity (Some T); [apply map_lookup_union_Some_raw; left; exact HT|symmetry; exact HT].
  - intros m Hm. exists m. split; [apply res_restrict_le|].
    eapply ctx_denote_under_comma_left. exact Hm.
Qed.

(** Static weakening premises follow from source regularity and the final
    context's well-formedness; no refinement is reconstructed. *)
Lemma typing_comma_prefix_wf Φ Σ Γ Δ e τ :
  wf_ctx_under Σ (CtxComma Γ Δ) ->
  has_context_type Φ Σ Γ e τ ->
  has_context_type Φ Σ (CtxComma Γ Δ) e τ.
Proof.
  intros Hwf Hty.
  pose proof (typing_wf_under _ _ _ _ _ Hty) as [HΓ [Hτ He]].
  eapply CT_CtxSub; [|exact Hty|].
  - split; [exact Hwf|]. split.
    + eapply wf_context_ty_at_mono_env; [|exact Hτ].
      cbn [erase_ctx]. unfold store_union. rewrite dom_union_L. clear; set_solver.
    + eapply basic_typing_weaken_tm; [exact He|].
      apply map_subseteq_spec. intros x T Hx. cbn [erase_ctx].
      apply map_lookup_union_Some_raw. left. exact Hx.
  - apply ctx_sub_comma_prefix; [exact Hwf|].
    pose proof (basic_typing_contains_fv_tm _ _ _ He) as HeFV.
    pose proof (basic_context_ty_fv_subset _ _ Hτ) as HτFV.
    clear -HeFV HτFV. set_solver.
Qed.

Lemma typing_comma_prefix Φ Σ Γ Δ e τ :
  context_typing_wf Σ (CtxComma Γ Δ) e τ ->
  has_context_type Φ Σ Γ e τ ->
  has_context_type Φ Σ (CtxComma Γ Δ) e τ.
Proof.
  intros Hwf Hty. eapply CT_CtxSub; [exact Hwf|exact Hty|].
  apply ctx_sub_comma_prefix; [exact (proj1 Hwf)|].
  pose proof (typing_wf_under _ _ _ _ _ Hty) as Hsrc.
  pose proof (basic_typing_contains_fv_tm _ _ _ (proj2 (proj2 Hsrc))) as He.
  pose proof (basic_context_ty_fv_subset _ _ (proj1 (proj2 Hsrc))) as Hτ.
  set_solver.
Qed.
