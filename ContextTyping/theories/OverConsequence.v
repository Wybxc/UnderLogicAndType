(** Derived Over consequences.  The source remains a genuine typing
    derivation; these lemmas only supply the existing subsumption rule. *)
From Denotation Require Import Context TypeDenoteRegular TypeEquivCore TypeEquiv OverConsequence.
From ContextTyping Require Import Typing TypingRegular Subtyping SoundnessLam.

Lemma ctx_denote_under_store_scope Σ Γ (m : WfWorldT) σ :
  m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
  dom (erase_ctx Γ) ⊆ dom (σ : StoreT).
Proof.
  intros Hctx Hσ.
  change (dom (erase_ctx Γ) ⊆ (dom (σ : gmap atom value) : aset)).
  rewrite (wfworld_store_dom m σ Hσ).
  etransitivity; [apply ctx_erasure_under_erase_ctx_dom_subset|].
  apply basic_world_formula_atom_env_dom_subset.
  exact (ctx_denote_under_basic_world Σ Γ m Hctx).
Qed.

Lemma sub_type_over_store_consequence Σ Γ b φ1 φ2 :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTOver b φ1) ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTOver b φ2) ->
  (forall (m : WfWorldT) y σ v,
    m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    y ∉ world_dom (m : WorldT) ∪ qual_dom φ1 ∪ qual_dom φ2 ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ1)) (<[y:=v]> σ) ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ2)) (<[y:=v]> σ)) ->
  sub_type_under Σ Γ (CTOver b φ1) (CTOver b φ2).
Proof.
  intros HΓ Hwf1 Hwf2 Hmap.
  apply sub_type_under_intro; [exact HΓ|exact Hwf1|exact Hwf2|reflexivity|].
  intros e m He Hctx Hsource.
  assert (Hwf : context_typing_wf Σ Γ e (CTOver b φ2))
    by (split; [exact HΓ|split; assumption]).
  pose proof (ty_denote_under_total Σ Γ _ e m Hsource) as Htotal.
  assert (Hzero : m ⊨ ty_denote_gas 0 (atom_env_to_lty_env (erase_ctx Γ))
      (CTOver b φ2) e).
  { apply ty_denote_gas_zero_of_guard. apply ty_guard_relevant_of_static_full_total;
      [exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx)|exact Htotal]. }
  unfold ty_denote_under, ty_denote in Hsource |- *.
  eapply over_denote_store_consequence with (gas1:=0);
    [apply atom_store_to_lvar_store_closed|
     exact (context_typing_wf_lc_tm _ _ _ _ Hwf)|
     exact (wf_context_ty_at_lc 0 _ _ Hwf2)|exact Hsource|exact Hzero|].
  intros y σ v Hy Hσ Hq. exact (Hmap m y σ v Hctx Hσ Hy Hq).
Qed.

Lemma sub_type_under_inter_intro Σ Γ τ τ1 τ2 :
  sub_type_under Σ Γ τ τ1 -> sub_type_under Σ Γ τ τ2 ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTInter τ1 τ2) ->
  sub_type_under Σ Γ τ (CTInter τ1 τ2).
Proof.
  intros Hsub1 Hsub2 Hwf.
  destruct Hsub1 as [HΓ [Hτ [Hτ1 [Herase1 Hmap1]]]].
  destruct Hsub2 as [_ [_ [Hτ2 [Herase2 Hmap2]]]].
  apply sub_type_under_intro; [exact HΓ|exact Hτ|exact Hwf|exact Herase1|].
  intros e m He Hctx Hsource.
  pose proof (res_models_impl_elim m _ _ (Hmap1 e He m Hctx) Hsource) as H1.
  pose proof (res_models_impl_elim m _ _ (Hmap2 e He m Hctx) Hsource) as H2.
  assert (Hwf_e : context_typing_wf Σ Γ e (CTInter τ1 τ2)).
  { split; [exact HΓ|]. split; [exact Hwf|]. cbn [erase_ty]. rewrite <- Herase1. exact He. }
  pose proof (ty_denote_under_total Σ Γ _ e m Hsource) as Htotal.
  assert (Hguard : m ⊨ ty_guard_formula
    (relevant_env (atom_env_to_lty_env (erase_ctx Γ)) (CTInter τ1 τ2) e)
    (CTInter τ1 τ2) e).
  { apply ty_guard_relevant_of_static_full_total;
      [exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf_e Hctx)|exact Htotal]. }
  unfold ty_denote_under, ty_denote in H1, H2 |- *.
  cbn [cty_depth ty_denote_gas]. apply res_models_and_iff. split; [exact Hguard|].
  apply res_models_and_iff. split.
  - rewrite ty_denote_gas_saturate by lia. exact H1.
  - rewrite ty_denote_gas_saturate by lia. exact H2.
Qed.
