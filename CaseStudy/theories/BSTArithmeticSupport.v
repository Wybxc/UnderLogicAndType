(** Arithmetic qualifiers used by the original BST continuation. *)
From CaseStudy Require Import BSTNodeTypes BSTSupport NatArithmetic
  NatArithmeticTyping NatArithmeticApplications NatArithmeticStages.
From Denotation Require Import Context ResultQualifier QualifierStore.
From ContextTyping Require Import Typing Subtyping OverConsequence BasicBindings
  PrimOpConcreteContext PrimOpContext.
From ContextBasicDenotation Require Import TermEval.

Definition bst_pred_qual x : type_qualifier :=
  param_result_qual TNat {[x]}
    (fun s w => exists p, s !! x = Some (vnat p) /\ w = vnat (p-1)).

Lemma bst_pred_instantiate (σ : StoreT) x p :
  σ !! x = Some (vnat p) ->
  lstore_instantiate_tm (lstore_lift_free σ) (tprim op_minus1 (vfvar x)) =
    tprim op_minus1 (vnat p).
Proof.
  intros Hx. arithmetic_instantiate. setoid_rewrite Hx. reflexivity.
Qed.

Lemma bst_pred_primitive_context_typed Γ x :
  wf_ctx_under ∅ Γ -> erase_ctx Γ !! x = Some (TBase TNat) ->
  has_context_type concrete_Φ ∅ Γ (tprim op_minus1 (vfvar x))
    (CTOver TNat (bst_pred_qual x)).
Proof.
  intros HΓ Hx.
  assert (HxD : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (Hbasic : tm_has_type (erase_ctx Γ)
    (tprim op_minus1 (vfvar x)) (TBase TNat)).
  { eapply TT_Op; [reflexivity|apply VT_FVar; exact Hx]. }
  assert (Hlc : lc_tm (tprim op_minus1 (vfvar x))) by
    (eapply typing_tm_lc; exact Hbasic).
  assert (Hopened : wf_context_ty_at 0 (dom (erase_ctx Γ))
    ({0 ~> x} (primop_result_ty (concrete_Φ op_minus1)))).
  { eapply wf_context_ty_at_mono_env.
    2: { apply (wf_context_ty_at_open_at 0 ∅ _ x);
           [set_solver|apply primop_result_wf]. }
    clear -HxD. set_solver. }
  assert (Hprim : has_context_type concrete_Φ ∅ Γ
    (tprim op_minus1 (vfvar x))
    (precise_ty TNat (expr_result_qual (tprim op_minus1 (vfvar x)) (LVBound 0)))).
  { rewrite <- primop_graph_qual_open_arg.
    change (has_context_type concrete_Φ ∅ Γ (tprim op_minus1 (vfvar x))
      (precise_ty TNat (qual_open_atom 1 x (primop_graph_qual op_minus1)))).
    rewrite <- (primop_result_ty_open_eq op_minus1 x).
    apply CT_AppOp.
    - split; [exact HΓ|]. split; [exact Hopened|exact Hbasic].
    - rewrite primop_arg_ty_eq. apply typing_over_top_var; assumption. }
  assert (Htarget : wf_context_ty_at 0 (dom (erase_ctx Γ))
    (CTOver TNat (bst_pred_qual x))).
  { unfold bst_pred_qual. apply param_result_qual_wf. clear -HxD. set_solver. }
  eapply CT_Sub.
  - split; [exact HΓ|]. split; [exact Htarget|exact Hbasic].
  - exact (typing_inter_l _ _ _ _ _ _ Hprim).
  - apply sub_type_over_store_consequence; [exact HΓ| |exact Htarget|].
    + rewrite primop_result_ty_open_eq,primop_graph_qual_open_arg in Hopened.
      exact (proj1 Hopened).
    + intros m y σ w Hctx Hσ Hy Hq.
      assert (Hyx : y <> x).
      { unfold bst_pred_qual in Hy. rewrite param_result_qual_dom in Hy.
        clear -Hy. set_solver. }
      destruct (ctx_denote_under_lookup_typed ∅ Γ x _ m σ HΓ Hx Hctx Hσ)
        as [vx [Hvx Htx]].
      destruct (basic_typing_nat_canonical_form _ Htx) as [p ->].
      apply qualifier_holds_store_typed_result_qual_elim in Hq.
      rewrite opened_expr_result_qual in Hq by
        (first [exact Hlc|cbn [fv_tm fv_value]; clear -Hyx; set_solver]).
      destruct (expr_result_qual_store_elim _ _ _ Hq) as [v [Hyv Heval]].
      assert (Hxp : (<[y:=w]> σ : StoreT) !! x = Some (vnat p)).
      { rewrite store_insert_lookup_ne by congruence. exact Hvx. }
      unfold tm_eval_in_store,expr_eval_in_store in Heval.
      rewrite (bst_pred_instantiate _ _ _ Hxp) in Heval.
      destruct (reduction_prim_const _ _ _ Heval) as [c [Hstep ->]].
      inversion Hstep; subst c.
      assert (Hw : w = vnat (Nat.pred p)).
      { assert (Hsame : Some w = Some (vnat (Nat.pred p))).
        { transitivity ((<[y:=w]> σ : StoreT) !! y);
            [symmetry; apply map_lookup_insert|exact Hyv]. }
        now inversion Hsame. }
      subst w. unfold bst_pred_qual.
      apply typed_param_result_qual_open_store; [clear -Hyx; set_solver|].
      split.
      * pose proof (ctx_denote_under_store_scope ∅ Γ m σ Hctx Hσ) as HD.
        rewrite store_insert_dom. clear -HxD HD. set_solver.
      * exists (vnat (Nat.pred p)). split; [apply map_lookup_insert|].
        split; [apply BVT_Const|]. exists p. split.
        -- rewrite store_restrict_lookup_at by set_solver. exact Hxp.
        -- f_equal. lia.
Qed.

Definition nat_graph_store_result f u v (s : StoreT) w : Prop :=
  exists n k, s !! u = Some (vnat n) /\ s !! v = Some (vnat k) /\ w = vnat (f n k).

Lemma q_nat_graph_free_param f u v :
  q_nat_graph f (LVFree u) (LVFree v) (LVBound 0) =
    param_result_qual TNat {[u;v]} (nat_graph_store_result f u v).
Proof.
  apply qual_ext.
  - cbn [q_nat_graph param_result_qual qual_lvars].
    assert (H : lvars_of_atoms {[u;v]} = {[LVFree u;LVFree v]}).
    { apply set_eq. intros z. unfold lvars_of_atoms. rewrite elem_of_map. set_solver. }
    rewrite H. set_solver.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [q_nat_graph param_result_qual qual_prop qual_lvars lso_store storeAO_store].
    rewrite Hs. unfold nat_graph_store_result, lstore_free_part.
    rewrite !lstore_to_store_lookup. split.
    + intros [n [k [Hn [Hk Hnk]]]]. exists (vnat (f n k)).
      split; [exact Hnk|]. split; [apply BVT_Const|]. exists n, k. auto.
    + intros [w [Hw [_ [n [k [Hn [Hk ->]]]]]]]. exists n, k. auto.
Qed.

Lemma bst_root_arithmetic_subtype Σ Γ S u p a :
  wf_ctx_under Σ Γ -> S ⊆ dom (erase_ctx Γ) -> u ∈ S ->
  p ∈ dom (erase_ctx Γ) -> p ∉ S ->
  (forall m σ, m ⊨ ctx_denote_under Σ Γ -> (m : WorldT) σ ->
    σ !! u = Some (vnat a)) ->
  sub_type_under Σ Γ
    (CTOver TNat (q_nat_graph Nat.add (LVFree u) (LVFree p) (LVBound 0)))
    (CTOver TNat (bst_root_qual S p a)).
Proof.
  intros HΓ HS Hu Hp HpS Hfixed. apply sub_type_over_store_consequence.
  - exact HΓ.
  - exact (proj1 (nat_graph_wf 0 _ Nat.add u p (HS u Hu) Hp)).
  - unfold bst_root_qual. apply param_result_qual_wf. clear -HS Hp. set_solver.
  - intros m y σ w Hctx Hσ Hy Hq.
    assert (HySp : y ∉ S ∪ {[p]}).
    { unfold bst_root_qual in Hy. rewrite param_result_qual_dom in Hy.
      clear -Hy. set_solver. }
    assert (Hyup : y ∉ ({[u;p]} : aset)) by (clear -HySp Hu; set_solver).
    rewrite q_nat_graph_free_param in Hq.
    apply typed_param_result_qual_open_store in Hq; [|exact Hyup].
    destruct Hq as [_ [w' [Hyw [_ [n [k [Hn [Hk Hw']]]]]]]].
    rewrite !store_restrict_lookup_at in Hn, Hk by set_solver.
    rewrite store_insert_lookup_ne in Hn by (clear -HySp Hu; set_solver).
    pose proof (Hfixed m σ Hctx Hσ) as Ha.
    assert (Hna : n = a).
    { assert (H : Some (vnat n) = Some (vnat a)).
      { transitivity (σ !! u); [symmetry; exact Hn|exact Ha]. }
      now inversion H. }
    subst n.
    subst w'.
    assert (Hw : w = vnat (a+k)).
    { assert (H : Some w = Some (vnat (a+k))).
      { transitivity ((<[y:=w]> σ : StoreT) !! y);
          [symmetry; apply map_lookup_insert|exact Hyw]. }
      now inversion H. }
    subst w.
    unfold bst_root_qual. apply typed_param_result_qual_open_store; [exact HySp|].
    split.
    + pose proof (ctx_denote_under_store_scope Σ Γ m σ Hctx Hσ) as HD.
      rewrite store_insert_dom. clear -HS Hp HD. set_solver.
    + exists (vnat (a+k)). split; [apply map_lookup_insert|].
      split; [apply BVT_Const|]. exists k, (a+k). split.
      * rewrite store_restrict_lookup_at by set_solver. exact Hk.
      * auto.
Qed.

Lemma bst_root_arithmetic_context_typed Φ Γ S u p a :
  wf_ctx_under ∅ Γ -> S ⊆ dom (erase_ctx Γ) -> u ∈ S ->
  p ∉ S -> erase_ctx Γ !! u = Some (TBase TNat) ->
  erase_ctx Γ !! p = Some (TBase TNat) ->
  (forall m σ, m ⊨ ctx_denote_under ∅ Γ -> (m : WorldT) σ ->
    σ !! u = Some (vnat a)) ->
  has_context_type Φ ∅ Γ
    (NatArithmetic.app2 NatArithmetic.add_value (vfvar u) (vfvar p))
    (CTOver TNat (bst_root_qual S p a)).
Proof.
  intros HΓ HS Hu HpS Hlookupu Hlookupp Hfixed.
  assert (Hup : u <> p) by (clear -Hu HpS; set_solver).
  assert (Hp : p ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  eapply CT_Sub.
  - split; [exact HΓ|]. split.
    + unfold bst_root_qual. apply param_result_qual_wf. clear -HS Hp. set_solver.
    + exact (arithmetic_app2_basic true (erase_ctx Γ) u p Hlookupu Hlookupp).
  - exact (arithmetic_app2_over_context_typed Φ Γ true u p HΓ Hup Hlookupu Hlookupp).
  - apply bst_root_arithmetic_subtype; assumption.
Qed.
