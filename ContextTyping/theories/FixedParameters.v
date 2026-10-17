(** Derived under subtyping with fixed parameters.  The semantic bridge
    transports an existing type; it is not a semantic-to-syntax oracle. *)
From Denotation Require Import Context TypeDenote TypeDenoteRegular TypeEquivCore TypeEquiv FixedParameters.
From ContextTyping Require Import Typing TypingRegular Subtyping SoundnessLam.

Lemma sub_type_under_pointwise_fixed Σ Γ b φ1 φ2 F σfix :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTUnder b φ1) ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTUnder b φ2) ->
  qual_dom φ1 ⊆ F -> qual_dom φ2 ⊆ F ->
  (forall m σ, m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    store_restrict σ F = σfix) ->
  (forall y τ, y ∉ F -> store_restrict τ F = σfix ->
    (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ1)) τ <->
     qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ2)) τ)) ->
  sub_type_under Σ Γ (CTUnder b φ1) (CTUnder b φ2).
Proof.
  intros HΓ Hwf1 Hwf2 HF1 HF2 Hfixed Hequiv.
  apply sub_type_under_intro; [exact HΓ|exact Hwf1|exact Hwf2|reflexivity|].
  intros e m He Hctx Hsource.
  assert (Hwf : context_typing_wf Σ Γ e (CTUnder b φ2))
    by (split; [exact HΓ|split; assumption]).
  pose proof (ty_denote_under_total Σ Γ _ e m Hsource) as Htotal.
  assert (Hzero : m ⊨ ty_denote_gas 0 (atom_env_to_lty_env (erase_ctx Γ))
      (CTUnder b φ2) e).
  { apply ty_denote_gas_zero_of_guard. apply ty_guard_relevant_of_static_full_total;
      [exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx)|exact Htotal]. }
  unfold ty_denote_under, ty_denote in Hsource |- *.
  eapply under_denote_fixed_parameters with (gas1:=0) (F:=F) (σfix:=σfix);
    [apply atom_store_to_lvar_store_closed|
     exact (context_typing_wf_lc_tm _ _ _ _ Hwf)|
     exact (wf_context_ty_at_lc 0 _ _ Hwf1)|exact (wf_context_ty_at_lc 0 _ _ Hwf2)|
     exact HF1|exact HF2| |exact Hequiv|exact Hsource|exact Hzero].
  intros σ Hσ. exact (Hfixed m σ Hctx Hσ).
Qed.

(** The fixed assignment may be chosen after the context model is given.
    This is useful for a fiber with extra variables, without constructing
    a global finite map or fixing the higher-order library value. *)
Lemma sub_type_under_worldwise_fixed Σ Γ b φ1 φ2 F :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTUnder b φ1) ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTUnder b φ2) ->
  qual_dom φ1 ⊆ F -> qual_dom φ2 ⊆ F ->
  (forall m, m ⊨ ctx_denote_under Σ Γ -> exists σfix,
    (forall σ, (m : WorldT) σ -> store_restrict σ F = σfix) /\
    (forall y τ, y ∉ F -> store_restrict τ F = σfix ->
      (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ1)) τ <->
       qualifier_holds_store (qual_open_atom 0 y (typed_result_qual b φ2)) τ))) ->
  sub_type_under Σ Γ (CTUnder b φ1) (CTUnder b φ2).
Proof.
  intros HΓ Hwf1 Hwf2 HF1 HF2 Hfixed.
  apply sub_type_under_intro; [exact HΓ|exact Hwf1|exact Hwf2|reflexivity|].
  intros e m He Hctx Hsource.
  destruct (Hfixed m Hctx) as [σfix [Hassignment Hequiv]].
  assert (Hwf : context_typing_wf Σ Γ e (CTUnder b φ2))
    by (split; [exact HΓ|split; assumption]).
  pose proof (ty_denote_under_total Σ Γ _ e m Hsource) as Htotal.
  assert (Hzero : m ⊨ ty_denote_gas 0 (atom_env_to_lty_env (erase_ctx Γ))
      (CTUnder b φ2) e).
  { apply ty_denote_gas_zero_of_guard. apply ty_guard_relevant_of_static_full_total;
      [exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx)|exact Htotal]. }
  unfold ty_denote_under, ty_denote in Hsource |- *.
  eapply under_denote_fixed_parameters with (gas1:=0) (F:=F) (σfix:=σfix);
    [apply atom_store_to_lvar_store_closed|
     exact (context_typing_wf_lc_tm _ _ _ _ Hwf)|
     exact (wf_context_ty_at_lc 0 _ _ Hwf1)|exact (wf_context_ty_at_lc 0 _ _ Hwf2)|
     exact HF1|exact HF2|exact Hassignment|exact Hequiv|exact Hsource|exact Hzero].
Qed.
