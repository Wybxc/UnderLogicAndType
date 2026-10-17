(** Persistence elimination for dependent context variables is derivable
    using context subsumption; no new primitive typing constructor is needed. *)
From Denotation Require Import Context PersistElim.
From ContextTyping Require Import Typing TypingRegular.

Lemma ctx_denote_unpersist_right Σ Γ x τ (m : WfWorldT) :
  lc_context_ty τ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x (CTPersist τ))) ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros Hτ Hctx.
  cbn [ctx_denote_under ctx_fv erase_ctx erase_ty fv_cty
    context_ty_lvars context_ty_lvars_at] in Hctx |- *.
  repeat rewrite res_models_and_iff in Hctx |- *.
  destruct Hctx as [Hworld [HΓ [Hwx Hden]]].
  split; [exact Hworld|]. split; [exact HΓ|]. split; [exact Hwx|].
  unfold ty_denote in Hden |- *. cbn [cty_depth] in Hden.
  eapply ty_denote_gas_persist_ret_fvar_elim; [|exact Hτ|exact Hden].
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma typing_persist_var_right Φ Σ Γ x τ :
  context_typing_wf Σ (CtxComma Γ (CtxBind x (CTPersist τ)))
    (tret (vfvar x)) (CTPersist τ) ->
  has_context_type Φ Σ (CtxComma Γ (CtxBind x (CTPersist τ)))
    (tret (vfvar x)) τ.
Proof.
  intros Hwf.
  pose proof Hwf as [HΓ [Hτ He]].
  assert (Hlc : lc_context_ty τ).
  { apply (wf_context_ty_at_lc 0
      (dom (erase_ctx (CtxComma Γ (CtxBind x (CTPersist τ))))) τ). exact Hτ. }
  assert (Hwf' : context_typing_wf Σ (CtxComma Γ (CtxBind x τ))
      (tret (vfvar x)) τ).
  { exact Hwf. }
  eapply CT_CtxSub; [exact Hwf|apply CT_VarR; exact Hwf'|].
  split; [exact HΓ|]. split; [exact HΓ|]. split.
  - intros y _. reflexivity.
  - intros m Hctx. exists m. split; [apply res_restrict_le|].
    apply ctx_denote_unpersist_right; assumption.
Qed.
