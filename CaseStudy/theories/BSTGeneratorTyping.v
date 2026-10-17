(** Context-typing components for the actual BST generator. *)
From CaseStudy Require Import CaseTypes BSTGenerator BSTGeneratorProgram BSTSpecFacts.
From CaseStudy Require Import BSTGeneratorUnfolding NatArithmeticUnfolding.
From CaseStudy Require Import BSTContext BSTSupport.
From CoreLang Require Import BasicTyping BasicTypingProps.
From ContextBasicDenotation Require Import TermSyntax TermEval StoreTyping.
From Denotation Require Import Context TypeEquivTermBase.
From ContextTyping Require Import Typing TypingRegular Subtyping NatCases PersistElim Conversion.

Lemma q_bst_zero_constant lo :
  q_tree_bst_range (vconst (cnat 0)) (vconst (cnat lo)) (vbvar 0) =
    mk_q_eq (vbvar 0) (vconst (ctree tr_leaf)).
Proof.
  apply qual_ext.
  - cbn [q_tree_bst_range mk_q_eq qual_lvars lvar_value_keys]. set_solver.
  - intros [s1 Hdom1] [s2 Hdom2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [q_tree_bst_range mk_q_eq qual_prop qual_lvars lvar_value_keys
      denote_lvar_value].
    cbn [lso_store storeAO_store].
    rewrite Hs. split.
    + intros [n [a [t [Hn [Ha [Ht Hbst]]]]]].
      inversion Hn; inversion Ha; subst n a.
      apply bst_spec_zero in Hbst. subst t. exact Ht.
    + intros Ht. exists 0%nat, lo, tr_leaf.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Ht|].
      apply bst_spec_zero. reflexivity.
Qed.

Lemma bst_leaf_context_typed Φ Σ Γ lo :
  wf_ctx_under Σ Γ ->
  has_context_type Φ Σ Γ (tret (vconst (ctree tr_leaf)))
    (under_ty TTree
      (q_tree_bst_range (vconst (cnat 0)) (vconst (cnat lo)) (vbvar 0))).
Proof.
  intros HΓ. rewrite q_bst_zero_constant.
  change (has_context_type Φ Σ Γ (tret (vconst (ctree tr_leaf)))
    (CTUnder (base_ty_of_const (ctree tr_leaf))
      (mk_q_eq (vbvar 0) (vconst (ctree tr_leaf))))).
  apply typing_inter_r with (τ1 := CTOver TTree
    (mk_q_eq (vbvar 0) (vconst (ctree tr_leaf)))).
  apply typing_const_in_ctx. split; [exact HΓ|].
  split; [apply const_precise_wf|apply TT_Ret, VT_Const].
Qed.

(** In the generator body [range] is a variable of the persistent library
    type.  The ordinary function type needed by application is derivable. *)
Definition bst_range_function_ty : context_ty :=
  CTArrow (over_ty TNat qual_top)
    (CTArrow (over_ty TNat (q_nat_le arg0 ν))
      (precise_ty TNat (qual_and (q_nat_le arg1 ν) (q_nat_le ν arg0)))).

Lemma bst_range_context_elim Φ Σ Γ g :
  context_typing_wf Σ (CtxComma Γ (CtxBind g range_ty))
    (tret (vfvar g)) range_ty ->
  has_context_type Φ Σ (CtxComma Γ (CtxBind g range_ty))
    (tret (vfvar g)) bst_range_function_ty.
Proof. intros Hwf. apply typing_persist_var_right. exact Hwf. Qed.

Lemma bst_ctx_lookup_typed Σ Γ x T (m : WfWorld) σ :
  wf_ctx_under Σ Γ -> erase_ctx Γ !! x = Some T ->
  m ⊨ ctx_denote_under Σ Γ -> (m : World) σ ->
  exists v, σ !! x = Some v /\ value_has_type ∅ v T.
Proof.
  intros HΓ Hx Hctx Hσ.
  assert (Hxdom : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hxenv : ctx_erasure_under Σ Γ !! x = Some T).
  { rewrite <- (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx Σ Γ x HΓ Hxdom).
    exact Hx. }
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope [_ Hstores]]].
  assert (Hxd : x ∈ world_dom (m : World)).
  { apply Hscope. rewrite lvars_fv_atom_env_to_lty_env_dom. apply elem_of_dom; eauto. }
  assert (Hxdσ : x ∈ dom (σ : gmap atom value)).
  { rewrite (wfworld_store_dom m σ Hσ). exact Hxd. }
  apply elem_of_dom in Hxdσ as [v Hv]. exists v. split; [exact Hv|].
  pose proof (Hstores (lstore_lift_free σ)
    ltac:(exists σ; split; [exact Hσ|reflexivity])) as Hstore.
  apply (Hstore (LVFree x) T v).
  - rewrite atom_store_to_lvar_store_lookup_free. exact Hxenv.
  - rewrite lstore_lift_free_lookup_free. exact Hv.
Qed.

(** A genuine typing derivation for the zero-size call.  The source
    derivation is [ret Leaf]; certified finite reductions transport it to
    the actual fixed-point application.  The range variable is arbitrary. *)
Lemma bst_zero_call_context_typed Φ Σ Γ lo g :
  wf_ctx_under Σ Γ ->
  erase_ctx Γ !! g = Some (TNat →ᵦ TNat →ᵦ TNat) ->
  has_context_type Φ Σ Γ
    (NatArithmetic.app3 bst_gen_value (vnat 0) (vnat lo) (vfvar g))
    (under_ty TTree
      (q_tree_bst_range (vconst (cnat 0)) (vconst (cnat lo)) (vbvar 0))).
Proof.
  intros HΓ Hg.
  eapply CT_Conv; [|apply bst_leaf_context_typed; exact HΓ|].
  - split; [exact HΓ|]. split.
    + rewrite q_bst_zero_constant.
      exact (proj1 (proj2 (const_precise_wf 0 (dom (erase_ctx Γ)) (ctree tr_leaf)))).
    + apply bst_call_basic_typed. apply VT_FVar. exact Hg.
  - intros m Hctx. split.
    + intros σ v Hσ.
      destruct (bst_ctx_lookup_typed Σ Γ g _ m σ HΓ Hg Hctx Hσ)
        as [vg [Hvg Htyped]].
      destruct (arithmetic_prefix_equivalence _ _
        (bst_zero_call_prefix ∅ lo vg Htyped)) as [Hrun _].
      unfold tm_eval_in_store, expr_eval_in_store.
      rewrite (bst_call_instantiate σ 0 lo g vg Hvg (typing_value_lc _ _ _ Htyped)).
      rewrite instantiate_closed_tm by reflexivity. symmetry. apply Hrun.
    + intros σ Hσ.
      destruct (bst_ctx_lookup_typed Σ Γ g _ m σ HΓ Hg Hctx Hσ)
        as [vg [Hvg Htyped]].
      destruct (arithmetic_prefix_equivalence _ _
        (bst_zero_call_prefix ∅ lo vg Htyped)) as [_ Htotal].
      rewrite (bst_call_instantiate σ 0 lo g vg Hvg (typing_value_lc _ _ _ Htyped)).
      rewrite instantiate_closed_tm by reflexivity. symmetry. exact Htotal.
Qed.

(** Change the actual arguments only after the context fixes their values.
    The source is a syntax derivation for the same closed generator. *)
Lemma bst_call_variables_context_conv Φ Σ Γ n a u v g τ :
  erase_ctx Γ !! u = Some (TBase TNat) ->
  erase_ctx Γ !! v = Some (TBase TNat) ->
  erase_ctx Γ !! g = Some (TNat →ᵦ TNat →ᵦ TNat) ->
  erase_ty τ = TBase TTree ->
  (forall m σ, m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a)) ->
  has_context_type Φ Σ Γ
    (NatArithmetic.app3 bst_gen_value (vnat n) (vnat a) (vfvar g)) τ ->
  has_context_type Φ Σ Γ
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g)) τ.
Proof.
  intros Hu Hv Hg Herase Hfixed Hsource.
  pose proof (typing_wf_under _ _ _ _ _ Hsource) as [HΓ [Hτ He]].
  eapply CT_Conv; [|exact Hsource|].
  - split; [exact HΓ|]. split; [exact Hτ|]. rewrite Herase.
    apply bst_call_variables_basic_typed; assumption.
  - intros m Hctx. split.
    + intros σ w Hσ.
      destruct (Hfixed m σ Hctx Hσ) as [Hun Hva].
      destruct (bst_ctx_lookup_typed Σ Γ g _ m σ HΓ Hg Hctx Hσ)
        as [vg [Hvg Htyped]].
      pose proof (typing_value_lc _ _ _ Htyped) as Hlc.
      unfold tm_eval_in_store, expr_eval_in_store.
      rewrite (bst_call_instantiate σ n a g vg Hvg Hlc),
        (bst_call_variables_instantiate σ n a u v g vg Hun Hva Hvg Hlc).
      reflexivity.
    + intros σ Hσ.
      destruct (Hfixed m σ Hctx Hσ) as [Hun Hva].
      destruct (bst_ctx_lookup_typed Σ Γ g _ m σ HΓ Hg Hctx Hσ)
        as [vg [Hvg Htyped]].
      pose proof (typing_value_lc _ _ _ Htyped) as Hlc.
      rewrite (bst_call_instantiate σ n a g vg Hvg Hlc),
        (bst_call_variables_instantiate σ n a u v g vg Hun Hva Hvg Hlc).
      reflexivity.
Qed.

(** The n=0 case of the actual minimal-context induction, with variable
    inputs and the original free-parameter BST qualifier. *)
Lemma bst_zero_call_minimal_context_typed Φ a u v g :
  u <> v -> u <> g -> v <> g ->
  has_context_type Φ ∅ (bst_call_ctx 0 a u v g)
    (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  intros Huv Hug Hvg.
  pose proof (bst_call_ctx_wf 0 a u v g Huv Hug Hvg) as HΓ.
  destruct (bst_call_ctx_lookups 0 a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  assert (HuD : u ∈ dom (erase_ctx (bst_call_ctx 0 a u v g)))
    by (eapply elem_of_dom_2; exact Hu).
  assert (HvD : v ∈ dom (erase_ctx (bst_call_ctx 0 a u v g)))
    by (eapply elem_of_dom_2; exact Hv).
  eapply CT_Sub with (τ1:=CTUnder TTree
    (q_tree_bst_range (vnat 0) (vnat a) (vbvar 0))).
  - split; [exact HΓ|]. split.
    + apply q_bst_free_wf; assumption.
    + apply bst_call_variables_basic_typed; assumption.
  - eapply bst_call_variables_context_conv;
      [exact Hu|exact Hv|exact Hg|reflexivity| |].
    + intros m σ Hctx Hσ. exact (bst_call_ctx_lookup 0 a u v g m σ Hctx Hσ).
    + apply bst_zero_call_context_typed; assumption.
  - apply q_bst_constants_subtype; [exact HΓ|exact HuD|exact HvD|].
    intros m σ Hctx Hσ. exact (bst_call_ctx_lookup 0 a u v g m σ Hctx Hσ).
Qed.
