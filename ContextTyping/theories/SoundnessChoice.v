(** Soundness of under choice through conditional result coverage. *)
From CoreLang Require Import Choice.
From Denotation Require Import Context TypeDenote Choice.
From ContextTyping Require Import Typing TypingRegular SoundnessLam.

Lemma fundamental_choose_under_case Σ Γ left right b φ :
  context_typing_wf Σ Γ (choose_tm left right) (CTUnder b φ) ->
  context_typing_wf Σ Γ left (CTOver b qual_top) ->
  context_typing_wf Σ Γ right (CTUnder b φ) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTOver b qual_top) left) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTUnder b φ) right) ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ (CTUnder b φ) (choose_tm left right).
Proof.
  intros Hwf HwfL HwfR HL HR m Hctx.
  specialize (HL m Hctx). specialize (HR m Hctx).
  unfold ty_denote_under, ty_denote in HL, HR |- *.
  eapply choose_under_denotation with (gasR := 0).
  - apply atom_store_to_lvar_store_closed.
  - exact (context_typing_wf_lc_tm _ _ _ _ HwfL).
  - exact (context_typing_wf_lc_tm _ _ _ _ HwfR).
  - exact (wf_context_ty_at_lc 0 _ _ (context_typing_wf_context_ty _ _ _ _ Hwf)).
  - exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx).
  - exact HL.
  - exact HR.
Qed.
