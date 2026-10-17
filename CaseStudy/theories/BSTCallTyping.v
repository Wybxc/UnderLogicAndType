(** Strong induction for applications of the original closed generator. *)
From CaseStudy Require Import BSTGeneratorProgram BSTGeneratorUnfolding
  BSTGeneratorTyping BSTContext BSTSupport BSTPositiveTyping NatArithmeticStages.
From ContextTyping Require Import Typing TypingRegular PrimOpConcreteContext BasicBindings.
From ContextBasicDenotation Require Import TermSyntax TermEval.
From Denotation Require Import Context TypeEquivTermBase.
From CoreLang Require Import BasicTypingProps.

Lemma bst_positive_branch_instantiate σ n a u v g f :
  σ !! u = Some (vnat n) -> σ !! v = Some (vnat a) ->
  σ !! g = Some f -> lc_value f ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (bst_positive_branch (vfvar u) (vfvar v) (vfvar g)) =
  bst_positive_branch (vnat n) (vnat a) f.
Proof.
  intros Hu Hv Hg Hf.
  arithmetic_instantiate. setoid_rewrite Hu. setoid_rewrite Hv. setoid_rewrite Hg.
  vm_compute. repeat rewrite open_rec_lc_value by exact Hf.
  reflexivity.
Qed.

Lemma bst_positive_call_minimal_context_typed n a u v g :
  0 < n -> u <> v -> u <> g -> v <> g -> bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_call_ctx n a u v g)
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  intros Hn Huv Hug Hvg HIH. destruct n as [|n]; [lia|].
  pose proof (bst_positive_branch_context_typed (S n) a u v g Hn Huv Hug Hvg HIH) as Hbranch.
  pose proof (typing_wf_under _ _ _ _ _ Hbranch) as [HΓ [Hτ _]].
  destruct (bst_call_ctx_lookups (S n) a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  eapply CT_Conv; [|exact Hbranch|].
  - split; [exact HΓ|]. split; [exact Hτ|].
    apply bst_call_variables_basic_typed; assumption.
  - intros m Hctx.
    assert (Hargs : forall σ, (m : WorldT) σ -> exists f,
      σ !! u = Some (vnat (S n)) /\ σ !! v = Some (vnat a) /\
      σ !! g = Some f /\ value_has_type ∅ f BSTProgram.range_basic_ty).
    { intros σ Hσ.
      destruct (bst_call_ctx_lookup (S n) a u v g m σ Hctx Hσ) as [Hun Hva].
      destruct (ctx_denote_under_lookup_typed ∅ _ g _ m σ HΓ Hg Hctx Hσ)
        as [f [Hgf Hft]].
      exists f. auto. }
    split.
    + intros σ w Hσ. destruct (Hargs σ Hσ) as [f [Hun [Hva [Hgf Hft]]]].
      pose proof (typing_value_lc _ _ _ Hft) as Hflc.
      unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (bst_positive_branch_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc),
        (bst_call_variables_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc).
      symmetry. exact (proj1 (arithmetic_prefix_equivalence _ _
        (bst_positive_call_prefix ∅ n a f Hft)) w).
    + intros σ Hσ. destruct (Hargs σ Hσ) as [f [Hun [Hva [Hgf Hft]]]].
      pose proof (typing_value_lc _ _ _ Hft) as Hflc.
      rewrite (bst_positive_branch_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc),
        (bst_call_variables_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc).
      symmetry. exact (proj2 (arithmetic_prefix_equivalence _ _
        (bst_positive_call_prefix ∅ n a f Hft))).
Qed.

(** Every induction hypothesis is a derivation for the same actual value,
    with arbitrary lower bound and fresh names.  No recursive self contract
    is assumed in a mixed world. *)
Theorem bst_call_minimal_context_typed n :
  forall a u v g, u <> v -> u <> g -> v <> g ->
  has_context_type concrete_Φ ∅ (bst_call_ctx n a u v g)
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  induction n using lt_wf_ind. intros a u v g Huv Hug Hvg.
  destruct n as [|n].
  - apply bst_zero_call_minimal_context_typed; assumption.
  - apply bst_positive_call_minimal_context_typed; try assumption; [lia|].
    intros m a' u' v' g' Hm Huv' Hug' Hvg'.
    exact (H m Hm a' u' v' g' Huv' Hug' Hvg').
Qed.

Lemma bst_open_body_instantiate σ n a u v g f :
  σ !! u = Some (vnat n) -> σ !! v = Some (vnat a) ->
  σ !! g = Some f -> lc_value f ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (bst_open_body (vfvar u) (vfvar v) (vfvar g)) =
  bst_open_body (vnat n) (vnat a) f.
Proof.
  intros Hu Hv Hg Hf.
  arithmetic_instantiate. setoid_rewrite Hu. setoid_rewrite Hv. setoid_rewrite Hg.
  vm_compute. repeat rewrite open_rec_lc_value by exact Hf. reflexivity.
Qed.

Lemma bst_open_body_minimal_context_typed n a u v g :
  u <> v -> u <> g -> v <> g ->
  has_context_type concrete_Φ ∅ (bst_call_ctx n a u v g)
    (bst_open_body (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  intros Huv Hug Hvg.
  pose proof (bst_call_minimal_context_typed n a u v g Huv Hug Hvg) as Hcall.
  pose proof (typing_wf_under _ _ _ _ _ Hcall) as [HΓ [Hτ _]].
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  eapply CT_Conv; [|exact Hcall|].
  - split; [exact HΓ|]. split; [exact Hτ|].
    apply bst_open_body_variables_basic; assumption.
  - intros m Hctx.
    assert (Hargs : forall σ, (m : WorldT) σ -> exists f,
      σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\
      σ !! g = Some f /\ value_has_type ∅ f BSTProgram.range_basic_ty).
    { intros σ Hσ.
      destruct (bst_call_ctx_lookup n a u v g m σ Hctx Hσ) as [Hun Hva].
      destruct (ctx_denote_under_lookup_typed ∅ _ g _ m σ HΓ Hg Hctx Hσ)
        as [f [Hgf Hft]]. exists f. auto. }
    split.
    + intros σ w Hσ. destruct (Hargs σ Hσ) as [f [Hun [Hva [Hgf Hft]]]].
      pose proof (typing_value_lc _ _ _ Hft) as Hflc.
      unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (bst_open_body_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc),
        (bst_call_variables_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc).
      exact (proj1 (arithmetic_prefix_equivalence _ _ (bst_call_body_prefix ∅ n a f Hft)) w).
    + intros σ Hσ. destruct (Hargs σ Hσ) as [f [Hun [Hva [Hgf Hft]]]].
      pose proof (typing_value_lc _ _ _ Hft) as Hflc.
      rewrite (bst_open_body_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc),
        (bst_call_variables_instantiate _ _ _ _ _ _ _ Hun Hva Hgf Hflc).
      exact (proj2 (arithmetic_prefix_equivalence _ _ (bst_call_body_prefix ∅ n a f Hft))).
Qed.
