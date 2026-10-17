(** Soundness of node construction with conditional under coverage. *)
From Denotation Require Import Context TypeDenote TreeCoverage.
From ContextTyping Require Import Typing TypingRegular SoundnessLam.

Lemma fundamental_node_under_graph_case Σ Γ S xp xk xl xr φP φK φL φR Θ P K L R Q :
  context_typing_wf Σ Γ (tnode (vfvar xk) (vfvar xl) (vfvar xr)) (CTUnder TTree Θ) ->
  node_under_graph_spec S xp xk xl xr φP φK φL φR Θ P K L R Q ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTUnder TNat φP) (tret (vfvar xp))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTOver TNat φK) (tret (vfvar xk))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTUnder TTree φL) (tret (vfvar xl))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTUnder TTree φR) (tret (vfvar xr))) ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTUnder TTree Θ)
    (tnode (vfvar xk) (vfvar xl) (vfvar xr)).
Proof.
  intros Hwf Hspec HP HK HL HR m Hctx.
  specialize (HP m Hctx). specialize (HK m Hctx).
  specialize (HL m Hctx). specialize (HR m Hctx).
  unfold ty_denote_under, ty_denote in HP, HK, HL, HR |- *.
  eapply node_under_graph_denotation with (gas := 0).
  - apply atom_store_to_lvar_store_closed.
  - exact (wf_context_ty_at_lc 0 _ _ (context_typing_wf_context_ty _ _ _ _ Hwf)).
  - exact Hspec.
  - exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx).
  - exact HP.
  - exact HK.
  - exact HL.
  - exact HR.
Qed.
