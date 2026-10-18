(** The revised examples use existing T-AppOp with graph specifications. *)
From CaseStudy Require Import MayMustRevised MayMustBase.
From ContextTyping Require Import Typing TypingRegular BasicBindings Subtyping
  PrimOpContext PrimOpConcreteContext.
From Denotation Require Import Context QualifierStore ResultQualifier.
From CoreLang Require Import BasicTypingProps OperationalProps.

Lemma mm_prim_graph_wf Γ op x a b :
  prim_op_type op = (a,b) -> erase_ctx Γ !! x = Some (TBase a) ->
  wf_context_ty_at 0 (dom (erase_ctx Γ))
    (precise_ty b (expr_result_qual (tprim op (vfvar x)) (LVBound 0))).
Proof.
  intros Hop Hx.
  assert (HxD : x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  pose proof (primop_result_wf op) as Hwf.
  pose proof (wf_context_ty_at_open_at 0 ∅ _ x ltac:(set_solver) Hwf) as Hopen.
  rewrite primop_result_ty_open_eq in Hopen.
  destruct op; injection Hop as <- <-; rewrite primop_graph_qual_open_arg in Hopen.
  all: eapply wf_context_ty_at_mono_env; [|exact Hopen]; clear -HxD; set_solver.
Qed.

Lemma mm_prim_graph_typed Γ op x a b :
  prim_op_type op = (a,b) -> wf_ctx_under ∅ Γ ->
  erase_ctx Γ !! x = Some (TBase a) ->
  has_context_type concrete_Φ ∅ Γ (tprim op (vfvar x))
    (precise_ty b (expr_result_qual (tprim op (vfvar x)) (LVBound 0))).
Proof.
  intros Hop HΓ Hx.
  assert (Hopened : wf_context_ty_at 0 (dom (erase_ctx Γ))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))).
  { eapply wf_context_ty_at_mono_env.
    2: { apply (wf_context_ty_at_open_at 0 ∅ _ x);
      [set_solver|apply primop_result_wf]. }
    assert (x ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto). set_solver. }
  assert (Hprim : has_context_type concrete_Φ ∅ Γ (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))).
  { apply CT_AppOp.
    - split; [exact HΓ|]. split; [exact Hopened|].
      destruct op; injection Hop as <- <-.
      all: eapply TT_Op; [reflexivity|apply VT_FVar; exact Hx].
    - rewrite primop_arg_ty_eq. apply typing_over_top_var; [exact HΓ|].
      destruct op; injection Hop as <- <-; exact Hx. }
  rewrite primop_result_ty_open_eq in Hprim.
  destruct op; injection Hop as <- <-;
    rewrite primop_graph_qual_open_arg in Hprim; exact Hprim.
Qed.

Lemma mm_prim_over_typed Γ op x a b :
  prim_op_type op = (a,b) -> wf_ctx_under ∅ Γ ->
  erase_ctx Γ !! x = Some (TBase a) ->
  has_context_type concrete_Φ ∅ Γ (tprim op (vfvar x))
    (CTOver b (expr_result_qual (tprim op (vfvar x)) (LVBound 0))).
Proof.
  intros Hop HΓ Hx. apply typing_inter_l with
    (τ2:=CTUnder b (expr_result_qual (tprim op (vfvar x)) (LVBound 0))).
  exact (mm_prim_graph_typed Γ op x a b Hop HΓ Hx).
Qed.

Lemma mm_instantiate_prim_var s op x c :
  s !! x = Some (vconst c) ->
  lstore_instantiate_tm (lstore_lift_free s) (tprim op (vfvar x)) =
    tprim op (vconst c).
Proof.
  intros Hx. unfold lstore_instantiate_tm,lstore_instantiate_tm_at.
  cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
  rewrite lstore_free_part_lift_free.
  change (tprim op (match s !! x with Some v => v | None => vfvar x end) = tprim op (vconst c)).
  rewrite Hx. reflexivity.
Qed.

Lemma mm_gt_graph_lookup k a b (s : StoreT) z :
  a <> b -> s !! a = Some (vint z) ->
  qualifier_holds_store (qual_open_atom 0 b (typed_result_qual TBool
    (expr_result_qual (tprim (op_int_gt k) (vfvar a)) (LVBound 0)))) s ->
  s !! b = Some (vconst (cbool (Z.gtb z k))).
Proof.
  intros Hab Ha Hq.
  apply qualifier_holds_store_typed_result_qual_elim in Hq.
  assert (Hlc : lc_tm (tprim (op_int_gt k) (vfvar a))) by
    (apply LC_op; apply LC_fvar).
  rewrite (opened_expr_result_qual _ b Hlc
    ltac:(cbn [fv_tm fv_value]; clear -Hab; set_solver)) in Hq.
  destruct (expr_result_qual_store_elim _ _ _ Hq) as [v [Hb Heval]].
  unfold tm_eval_in_store,expr_eval_in_store in Heval.
  rewrite (mm_instantiate_prim_var s _ a (cint z) Ha) in Heval.
  destruct (reduction_prim_const _ _ _ Heval) as [c [Hstep ->]].
  inversion Hstep; subst. exact Hb.
Qed.
