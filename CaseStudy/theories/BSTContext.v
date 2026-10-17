(** Closed minimal contexts for the syntax induction on actual BST calls. *)
From CaseStudy Require Import CaseTypes BSTGenerator.
From Denotation Require Import Context PersistSubset.
From ContextTyping Require Import Typing TypingRegular NatCases ConstCases Weakening.

Lemma bst_range_ty_closed_wf : basic_context_ty ∅ range_ty.
Proof.
  cbn [basic_context_ty wf_context_ty_at range_ty over_ty precise_ty q_nat_le
    qual_and qual_vars qual_top_on arg0 arg1 vnu lvar_value_keys erase_ty].
  unfold lvars_wf_at. repeat split; try reflexivity.
  all: intros [k|x] H; cbn [lvar_wf_at] in *; set_solver by lia.
Qed.

Lemma bst_range_ty_fv : fv_cty range_ty = ∅.
Proof.
  pose proof (basic_context_ty_fv_subset ∅ range_ty bst_range_ty_closed_wf).
  set_solver.
Qed.

Definition bst_call_ctx n a u v g : ctx :=
  CtxComma (nat_pair_ctx u v (nat_singleton_ty n) (nat_singleton_ty a))
    (CtxBind g range_ty).

Lemma bst_call_ctx_wf n a u v g :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ (bst_call_ctx n a u v g).
Proof.
  intros Huv Hug Hvg. unfold bst_call_ctx, wf_ctx_under.
  split; [apply nat_pair_ctx_wf; [exact Huv|apply nat_singleton_wf|apply nat_singleton_wf]|].
  split.
  - split; [unfold nat_pair_ctx; cbn [ctx_dom]; set_solver|].
    eapply wf_context_ty_at_mono_env; [|exact bst_range_ty_closed_wf]. set_solver.
  - unfold nat_pair_ctx. cbn [ctx_dom]. set_solver.
Qed.

Lemma bst_call_ctx_denote_intro n a u v g (m : WfWorld) :
  u <> v ->
  m ⊨ ctx_denote_under ∅ (CtxBind u (nat_singleton_ty n)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind v (nat_singleton_ty a)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind g range_ty) ->
  m ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g).
Proof.
  intros Huv Hu Hv Hg. unfold bst_call_ctx.
  apply ctx_denote_under_comma_intro.
  - apply nat_pair_ctx_wf; [exact Huv|apply nat_singleton_wf|apply nat_singleton_wf].
  - apply nat_pair_denote_intro; [apply nat_singleton_wf|
      apply nat_singleton_fv|apply nat_singleton_fv|exact Hu|exact Hv].
  - rewrite ctx_denote_closed_env; [exact Hg|exact bst_range_ty_fv].
Qed.

Lemma bst_call_ctx_sub Γ n a u v g :
  wf_ctx_under ∅ Γ -> u <> v -> u <> g -> v <> g ->
  ty_env_agree_on {[u;v;g]} (erase_ctx Γ) (erase_ctx (bst_call_ctx n a u v g)) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ ->
    m ⊨ ctx_denote_under ∅ (CtxBind u (nat_singleton_ty n)) /\
    m ⊨ ctx_denote_under ∅ (CtxBind v (nat_singleton_ty a)) /\
    m ⊨ ctx_denote_under ∅ (CtxBind g range_ty)) ->
  ctx_sub_under ∅ {[u;v;g]} Γ (bst_call_ctx n a u v g).
Proof.
  intros HΓ Huv Hug Hvg Hagree Hbindings.
  split; [exact HΓ|]. split; [apply bst_call_ctx_wf; assumption|].
  split; [exact Hagree|]. intros m Hm. exists m. split; [apply res_restrict_le|].
  destruct (Hbindings m Hm) as [Hu [Hv Hg]].
  apply bst_call_ctx_denote_intro; assumption.
Qed.

Lemma ctx_denote_comma_closed_right Σ Γ x τ (m : WfWorld) :
  fv_cty τ = ∅ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x τ)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind x τ).
Proof.
  intros Hclosed Hctx.
  cbn [ctx_denote_under] in Hctx.
  apply res_models_and_iff in Hctx as [_ Hctx].
  apply res_models_and_iff in Hctx as [_ Hright].
  rewrite ctx_denote_closed_bind by exact Hclosed.
  cbn [ctx_fv] in Hright. rewrite Hclosed, storeA_restrict_empty_set in Hright.
  unfold store_union, store_empty in Hright. rewrite map_empty_union in Hright.
  exact Hright.
Qed.

Lemma bst_range_binding_fiber g X σ (m mfib : WfWorld) :
  m ⊨ ctx_denote_under ∅ (CtxBind g range_ty) ->
  res_fiber_from_projection m X σ mfib ->
  mfib ⊨ ctx_denote_under ∅ (CtxBind g range_ty).
Proof.
  intros Hrange Hfib. eapply ctx_bind_persist_res_subset; [|exact Hrange|].
  - split; [set_solver|exact bst_range_ty_closed_wf].
  - eapply res_subset_fiber_source; exact Hfib.
Qed.

Lemma bst_call_ctx_denote_inv n a u v g (m : WfWorld) :
  m ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g) ->
  m ⊨ ctx_denote_under ∅ (CtxBind u (nat_singleton_ty n)) /\
  m ⊨ ctx_denote_under ∅ (CtxBind v (nat_singleton_ty a)) /\
  m ⊨ ctx_denote_under ∅ (CtxBind g range_ty).
Proof.
  intros Hctx.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hpair.
  destruct (nat_pair_denote_inv ∅ u v _ _ m
    (nat_singleton_fv n) (nat_singleton_fv a) Hpair) as [Hu Hv].
  split; [exact Hu|]. split; [exact Hv|].
  eapply ctx_denote_comma_closed_right; [exact bst_range_ty_fv|exact Hctx].
Qed.

Lemma bst_call_ctx_lookup n a u v g (m : WfWorld) σ :
  m ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g) -> (m : World) σ ->
  σ !! u = Some (vconst (cnat n)) /\ σ !! v = Some (vconst (cnat a)).
Proof.
  intros Hctx Hσ. destruct (bst_call_ctx_denote_inv n a u v g m Hctx) as [Hu [Hv _]].
  split; eapply const_precise_bind_lookup; eassumption.
Qed.

Lemma bst_call_ctx_erasure n a u v g :
  erase_ctx (bst_call_ctx n a u v g) =
    ({[u:=TBase TNat]} ∪ {[v:=TBase TNat]}) ∪
      {[g:=TNat →ᵦ TNat →ᵦ TNat]}.
Proof.
  cbn [bst_call_ctx nat_pair_ctx erase_ctx nat_singleton_ty const_precise_ty
    precise_ty over_ty under_ty erase_ty base_ty_of_const range_ty].
  unfold store_union, store_empty. rewrite map_empty_union. reflexivity.
Qed.

Lemma bst_call_ctx_lookups n a u v g :
  u <> v -> u <> g -> v <> g ->
  erase_ctx (bst_call_ctx n a u v g) !! u = Some (TBase TNat) /\
  erase_ctx (bst_call_ctx n a u v g) !! v = Some (TBase TNat) /\
  erase_ctx (bst_call_ctx n a u v g) !! g = Some (TNat →ᵦ TNat →ᵦ TNat).
Proof.
  intros Huv Hug Hvg. rewrite bst_call_ctx_erasure. split.
  - apply map_lookup_union_Some_raw. left. apply map_lookup_union_Some_raw.
    left. apply map_lookup_singleton.
  - split.
    + apply map_lookup_union_Some_raw. left. apply map_lookup_union_Some_raw.
      right. split; [apply lookup_singleton_ne; congruence|apply map_lookup_singleton].
    + apply map_lookup_union_Some_raw. right. split.
      * apply map_lookup_union_None. split; apply lookup_singleton_ne; congruence.
      * apply map_lookup_singleton.
Qed.
