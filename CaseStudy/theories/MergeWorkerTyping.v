(** Direct independent-arrow typing of the original fixed-point worker. *)
From CaseStudy Require Import MergeIncorrectness MergeTraceTyping MergeReduction
  MayMustTyping NatArithmeticTyping.
From ContextTyping Require Import Typing TypingRegular Conversion BasicBindings
  PrimOpConcreteContext Soundness.
From Denotation Require Import Context TypeEquiv TypeEquivCore TypeEquivTermBase.

Definition merge_independent_one_ctx x :=
  CtxStar CtxEmpty (CtxBind x (merge_list_under sorted)).
Lemma merge_independent_one_wf x : wf_ctx_under ∅ (merge_independent_one_ctx x).
Proof.
  cbn [merge_independent_one_ctx wf_ctx_under basic_ctx ctx_dom].
  repeat split; try set_solver; apply merge_list_wf.
Qed.
Lemma merge_independent_one_erasure x :
  erase_ctx (merge_independent_one_ctx x) = {[x:=TBase TList]}.
Proof.
  cbn [merge_independent_one_ctx erase_ctx]. unfold store_union,store_empty.
  apply map_empty_union.
Qed.
Lemma merge_first_incorrect_context_typed x :
  has_context_type concrete_Φ ∅ (merge_independent_one_ctx x)
    (tapp_tm (tret IncorrectMerge.merge_value) (vfvar x))
    (CTWand (merge_list_under sorted) merge_error_result).
Proof.
  eapply CT_Conv; [|apply merge_inner_incorrect_context_typed|].
  - split; [apply merge_independent_one_wf|]. split.
    + split; [apply merge_list_wf|apply merge_error_wf].
    + eapply basic_typing_tapp_tm.
      * apply TT_Ret,merge_value_basic.
      * apply VT_FVar. rewrite merge_independent_one_erasure. apply map_lookup_singleton.
  - intros m Hctx.
    assert (Hlookup : forall s,(m : WorldT) s ->
      exists xs,s !! x=Some (IncorrectMerge.vlist xs)).
    { intros s Hs.
      destruct (ctx_denote_under_lookup_typed ∅ (merge_independent_one_ctx x) x (TBase TList) m s
        (merge_independent_one_wf x)
        ltac:(rewrite merge_independent_one_erasure; apply map_lookup_singleton) Hctx Hs)
        as [v [Hv Hty]].
      destruct (basic_typing_list_canonical_form v Hty) as [xs ->]. eauto. }
    split.
    + intros s v Hs. destruct (Hlookup s Hs) as [xs Hxs].
      unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (merge_partial_instantiate s x xs Hxs),(merge_first_instantiate s x xs Hxs).
      symmetry. exact (proj1 (arithmetic_prefix_equivalence _ _ (merge_first_prefix xs)) v).
    + intros s Hs. destruct (Hlookup s Hs) as [xs Hxs].
      rewrite (merge_partial_instantiate s x xs Hxs),(merge_first_instantiate s x xs Hxs).
      symmetry. exact (proj2 (arithmetic_prefix_equivalence _ _ (merge_first_prefix xs))).
Qed.

Theorem merge_worker_incorrect_context_typed :
  has_context_type concrete_Φ ∅ CtxEmpty
    (tret IncorrectMerge.merge_value) merge_incorrect_ty.
Proof.
  unfold merge_incorrect_ty. eapply CT_WandIntro with (L:=∅).
  - split; [constructor|]. split; [apply merge_incorrect_wf|apply TT_Ret,merge_value_basic].
  - intros x _. rewrite mm_closed_type_open by
      (split; [apply merge_list_wf|apply merge_error_wf]).
    apply merge_first_incorrect_context_typed.
Qed.
Corollary merge_worker_incorrect_context_sound :
  ctx_denote_under ∅ CtxEmpty ⊫ ty_denote_under ∅ CtxEmpty
    merge_incorrect_ty (tret IncorrectMerge.merge_value).
Proof. apply concrete_Fundamental,merge_worker_incorrect_context_typed. Qed.
Print Assumptions merge_worker_incorrect_context_typed.
Print Assumptions merge_worker_incorrect_context_sound.
