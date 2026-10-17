(** A base Under result can be joined over fibers contained in the term's
    and type's observable support.  This does not assert arrow joinability. *)
From Denotation Require Import Context TypeDenote TypeDenoteRegular
  TypePersistWandForward.
From ContextTyping Require Import Typing TypingRegular.

Lemma fv_under_qual b φ : fv_cty (CTUnder b φ) = qual_dom φ.
Proof.
  unfold fv_cty,context_ty_lvars. cbn [context_ty_lvars_at].
  rewrite lvars_fv_lvars_at_depth. reflexivity.
Qed.

Lemma context_under_fiberwise_joinable Σ Γ b φ e X :
  context_typing_wf Σ Γ e (CTUnder b φ) ->
  X ⊆ fv_tm e ∪ fv_cty (CTUnder b φ) ->
  fiberwise_joinable_on X (ty_denote_under Σ Γ (CTUnder b φ) e).
Proof.
  intros Hwf HX.
  pose proof (context_typing_wf_lc_tm _ _ _ _ Hwf) as Hlce.
  pose proof (context_typing_wf_basic_typing _ _ _ _ Hwf) as He.
  pose proof (basic_tm_has_ltype_lvars _ _ _
    (basic_tm_has_ltype_of_atom_env_typing _ _ _ He)) as Hevars.
  assert (HeΣ : tm_lvars e ⊆ dom (atom_env_to_lty_env (erase_ctx Γ))).
  { rewrite tm_lvars_lc_eq_atoms by exact Hlce. exact Hevars. }
  pose proof (proj1 (basic_context_ty_to_lvars _ _ (proj1 (proj2 Hwf)))) as Hτvars.
  assert (Hrel : relevant_lvars (CTUnder b φ) e ⊆
    dom (atom_env_to_lty_env (erase_ctx Γ))).
  { unfold relevant_lvars. rewrite atom_store_to_lvar_store_dom in HeΣ |- *.
    clear -HeΣ Hτvars. set_solver. }
  assert (HD : dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ)) (CTUnder b φ) e) =
    relevant_lvars (CTUnder b φ) e).
  { unfold relevant_env,lty_env_restrict_lvars.
    rewrite storeA_restrict_dom. unfold relevant_lvars in Hrel |- *.
    clear -Hrel. set_solver. }
  unfold ty_denote_under,ty_denote.
  eapply fiberwise_joinable_on_ty_denote_gas_under.
  - apply atom_store_to_lvar_store_closed.
  - exact Hlce.
  - rewrite HD. unfold relevant_lvars. set_solver.
  - rewrite HD,relevant_lvars_fv. clear -HX. set_solver.
Qed.
