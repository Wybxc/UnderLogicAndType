(** * Derived subtyping rules for the declarative context calculus. *)
From Denotation Require Import Context TypeEquiv TypeEquivCore TypeEquivFiberBaseCore.
From ContextTyping Require Import Typing TypingRegular.

Lemma context_typing_wf_denot_scope Σ Γ e τ (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  formula_scoped_in_world m (ty_denote_under Σ Γ τ e).
Proof.
  intros Hwf Hctx.
  pose proof (context_typing_wf_fv_tm_subset _ _ _ _ Hwf) as He.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf) as Hτ.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m
    (ctx_denote_under_basic_world Σ Γ m Hctx)) as Hdom.
  unfold formula_scoped_in_world, ty_denote_under, ty_denote.
  intros x Hx. apply ty_denote_gas_fv_subset in Hx.
  apply Hdom. rewrite ctx_erasure_under_minimal. set_solver.
Qed.

Lemma sub_type_under_intro Σ Γ τ1 τ2 :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ1 ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ2 ->
  erase_ty τ1 = erase_ty τ2 ->
  (forall e m, erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ1 ->
    m ⊨ ctx_denote_under Σ Γ ->
    m ⊨ ty_denote_under Σ Γ τ1 e ->
    m ⊨ ty_denote_under Σ Γ τ2 e) ->
  sub_type_under Σ Γ τ1 τ2.
Proof.
  intros HΓ H1 H2 Herase Hmap.
  split; [exact HΓ|]. split; [exact H1|]. split; [exact H2|].
  split; [exact Herase|]. intros e He m Hctx.
  apply res_models_impl_intro_scoped.
  - eapply (context_typing_wf_denot_scope Σ Γ); [repeat split; assumption|exact Hctx].
  - eapply (context_typing_wf_denot_scope Σ Γ); [|exact Hctx].
    repeat split; try assumption. rewrite <- Herase. exact He.
  - apply Hmap; assumption.
Qed.

Lemma sub_type_under_refl Σ Γ τ :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ ->
  sub_type_under Σ Γ τ τ.
Proof.
  intros HΓ Hτ. apply sub_type_under_intro; try assumption; auto.
Qed.

Lemma sub_type_under_trans Σ Γ τ1 τ2 τ3 :
  sub_type_under Σ Γ τ1 τ2 ->
  sub_type_under Σ Γ τ2 τ3 ->
  sub_type_under Σ Γ τ1 τ3.
Proof.
  intros [HΓ [H1 [H2 [H12 E12]]]] [_ [_ [H3 [H23 E23]]]].
  apply sub_type_under_intro; try assumption.
  - congruence.
  - intros e m He Hctx Hden.
    pose proof (res_models_impl_elim m _ _ (E12 e He m Hctx) Hden) as Hmid.
    assert (He2 : erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ2) by congruence.
    exact (res_models_impl_elim m _ _ (E23 e He2 m Hctx) Hmid).
Qed.

Lemma sub_type_under_inter_l Σ Γ τ1 τ2 :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTInter τ1 τ2) ->
  sub_type_under Σ Γ (CTInter τ1 τ2) τ1.
Proof.
  intros HΓ Hτ.
  apply sub_type_under_intro; try assumption; try reflexivity.
  - cbn [wf_context_ty_at] in Hτ. tauto.
  - intros e m He Hctx Hden.
    unfold ty_denote_under, ty_denote in *.
    cbn [cty_depth ty_denote_gas] in Hden.
    apply res_models_and_iff in Hden as [_ Hden].
    apply res_models_and_iff in Hden as [Hden _].
    rewrite ty_denote_gas_saturate in Hden by lia. exact Hden.
Qed.

Lemma sub_type_under_inter_r Σ Γ τ1 τ2 :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTInter τ1 τ2) ->
  sub_type_under Σ Γ (CTInter τ1 τ2) τ2.
Proof.
  intros HΓ Hτ.
  pose proof Hτ as [_ [H2 Herase]].
  apply sub_type_under_intro; try assumption.
  - intros e m He Hctx Hden.
    unfold ty_denote_under, ty_denote in *.
    cbn [cty_depth ty_denote_gas] in Hden.
    apply res_models_and_iff in Hden as [_ Hden].
    apply res_models_and_iff in Hden as [_ Hden].
    rewrite ty_denote_gas_saturate in Hden by lia. exact Hden.
Qed.

Lemma typing_inter_l Φ Σ Γ e τ1 τ2 :
  has_context_type Φ Σ Γ e (CTInter τ1 τ2) ->
  has_context_type Φ Σ Γ e τ1.
Proof.
  intros Hty.
  pose proof (typing_wf_under _ _ _ _ _ Hty) as [HΓ [Hτ He]].
  eapply CT_Sub; [|exact Hty|].
  - split; [exact HΓ|]. split; [exact (proj1 Hτ)|exact He].
  - apply sub_type_under_inter_l; assumption.
Qed.

Lemma typing_inter_r Φ Σ Γ e τ1 τ2 :
  has_context_type Φ Σ Γ e (CTInter τ1 τ2) ->
  has_context_type Φ Σ Γ e τ2.
Proof.
  intros Hty.
  pose proof (typing_wf_under _ _ _ _ _ Hty) as [HΓ [Hτ He]].
  destruct Hτ as [H1 [H2 Herase]].
  eapply CT_Sub; [|exact Hty|].
  - split; [exact HΓ|]. split; [exact H2|].
    cbn [erase_ty] in He. rewrite <- Herase. exact He.
  - apply sub_type_under_inter_r; [exact HΓ|].
    repeat split; assumption.
Qed.
