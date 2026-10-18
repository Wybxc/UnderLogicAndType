(** Both boolean outcomes, recovered from whole-world coverage. *)
From CaseStudy Require Import MayMustRevised MayMustWorlds MayMustBase MayMustPrimitives.
From ContextTyping Require Import Typing TypingRegular Subtyping BasicBindings NatCases ConstCases PrimOpConcreteContext.
From Denotation Require Import Context TypeEquiv TypeEquivCore.
From ContextLogic Require Import FormulaConnectives.
From Stdlib Require Import ZArith Lia.

Definition mm_bool_cases (b : atom) : ctx :=
  CtxSum (CtxBind b (bool_precise_ty true)) (CtxBind b (bool_precise_ty false)).

Lemma mm_bool_cases_wf b : wf_ctx_under ∅ (mm_bool_cases b).
Proof.
  split; [|split].
  - split; [set_solver|apply const_precise_wf].
  - split; [set_solver|apply const_precise_wf].
  - split; [reflexivity|reflexivity].
Qed.

Lemma mm_bool_world_lookup b (m : WfWorldT) s :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[b:=TBase TBool]}) ->
  (m : WorldT) s ->
  s !! b = Some (vconst (cbool true)) \/ s !! b = Some (vconst (cbool false)).
Proof.
  intros Hworld Hs.
  pose proof (over_top_bind_denote_from_basic_world b TBool m Hworld) as Hctx.
  destruct (ctx_denote_under_lookup_typed ∅ (CtxBind b (CTOver TBool qual_top))
    b (TBase TBool) m s ltac:(split; [set_solver|apply over_top_basic])
    ltac:(apply map_lookup_singleton) Hctx Hs) as [v [Hv Hty]].
  destruct (basic_typing_bool_canonical_form v Hty) as [Ht | Hf]; subst v; auto.
Qed.

Lemma mm_bool_partition b (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[b:=TBase TBool]}) ->
  (exists s, (m : WorldT) s /\ s !! b = Some (vconst (cbool true))) ->
  (exists s, (m : WorldT) s /\ s !! b = Some (vconst (cbool false))) ->
  m ⊨ ctx_denote_under ∅ (mm_bool_cases b).
Proof.
  intros Hworld Htrue [sf [Hsf Hfalse]].
  set (P := fun s : StoreT => s !! b = Some (vconst (cbool true))).
  assert (Hfalse' : exists s, (m : WorldT) s /\ ~ P s).
  { exists sf. split; [exact Hsf|]. unfold P. intros Hbad.
    pose proof (eq_trans (eq_sym Hfalse) Hbad) as Heq. discriminate Heq. }
  set (mt := select_world m P Htrue).
  set (mf := select_world m (fun s => ~P s) Hfalse').
  assert (Ht : mt ⊨ ctx_denote_under ∅ (CtxBind b (bool_precise_ty true))).
  { apply const_bind_denote_from_basic_world.
    - eapply basic_world_formula_res_subset; [apply select_world_subset|exact Hworld].
    - intros s [_ HP]. exact HP. }
  assert (Hf : mf ⊨ ctx_denote_under ∅ (CtxBind b (bool_precise_ty false))).
  { apply const_bind_denote_from_basic_world.
    - eapply basic_world_formula_res_subset; [apply select_world_subset|exact Hworld].
    - intros s [Hs HP].
      destruct (mm_bool_world_lookup b m s Hworld Hs); [contradiction|assumption]. }
  destruct (select_world_partition m P Htrue Hfalse') as [Hdef Heq].
  unfold mm_bool_cases. cbn [ctx_denote_under].
  apply res_models_and_iff. split.
  - change (m ⊨ basic_world_formula (atom_env_to_lty_env
      ((storeA_restrict (∅ : gmap atom ty) (ctx_fv (mm_bool_cases b))) ∪
        {[b:=TBase TBool]}))).
    unfold store_empty,store_union. rewrite storeA_restrict_empty,map_empty_union. exact Hworld.
  - eapply res_models_plus_intro with (m1:=mt) (m2:=mf) (Hdef:=Hdef).
    + unfold mt,mf. rewrite Heq. reflexivity.
    + exact Ht.
    + exact Hf.
Qed.

Lemma mm_ctx_sub_bool_cases Γ b X :
  wf_ctx_under ∅ Γ -> erase_ctx Γ !! b = Some (TBase TBool) ->
  X ⊆ ({[b]} : aset) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ ->
    (exists s, (m : WorldT) s /\ s !! b = Some (vconst (cbool true))) /\
    (exists s, (m : WorldT) s /\ s !! b = Some (vconst (cbool false)))) ->
  ctx_sub_under ∅ X Γ (mm_bool_cases b).
Proof.
  intros HΓ Hb HX Hcover.
  split; [exact HΓ|]. split; [apply mm_bool_cases_wf|]. split.
  - intros x Hx. apply HX,elem_of_singleton in Hx as ->.
    transitivity (Some (TBase TBool)); [exact Hb|symmetry; apply map_lookup_singleton].
  - intros m Hctx. exists m. split; [apply res_restrict_le|].
    destruct (Hcover m Hctx) as [Ht Hf]. apply mm_bool_partition; [|exact Ht|exact Hf].
    exact (ctx_denote_under_basic_singleton ∅ Γ b (TBase TBool) m HΓ Hb Hctx).
Qed.

Definition mm_gt_ty k a : context_ty :=
  CTOver TBool (expr_result_qual (tprim (op_int_gt k) (vfvar a)) (LVBound 0)).
Definition mm_positive_compare_ctx Γ a b k : ctx :=
  CtxComma (CtxComma Γ (CtxBind a (UInt (fun z => (0 < z)%Z))))
    (CtxBind b (mm_gt_ty k a)).

Lemma mm_positive_compare_covers Γ a b k (m : WfWorldT) :
  a <> b -> (1 <= k)%Z ->
  m ⊨ ctx_denote_under ∅ (mm_positive_compare_ctx Γ a b k) ->
  (exists s, (m : WorldT) s /\ s !! b = Some (vconst (cbool true))) /\
  (exists s, (m : WorldT) s /\ s !! b = Some (vconst (cbool false))).
Proof.
  intros Hab Hk Hctx.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hprefix.
  pose proof (mm_comma_closed_right ∅ Γ a (UInt (fun z => (0 < z)%Z))
    m (int_pred_fv false _) Hprefix) as Ha.
  destruct (int_bind_under_covers a (fun z => (0 < z)%Z) m (k+1)%Z Ha ltac:(cbn beta; lia)) as [st [Hst Hat]].
  destruct (int_bind_under_covers a (fun z => (0 < z)%Z) m 1%Z Ha ltac:(cbn beta; lia)) as [sf [Hsf Haf]].
  assert (Hq : forall s, (m : WorldT) s ->
    qualifier_holds_store (qual_open_atom 0 b (typed_result_qual TBool
      (expr_result_qual (tprim (op_int_gt k) (vfvar a)) (LVBound 0)))) s).
  { eapply mm_comma_over_store; [|exact Hctx].
    unfold qual_dom,expr_result_qual.
    cbn [qual_vars qual_lvars tm_lvars tm_lvars_at value_lvars_at bvar_lvars_at].
    rewrite lvars_fv_union,lvars_fv_singleton_free,lvars_fv_singleton_bound.
    clear -Hab. set_solver. }
  split.
  - exists st. split; [exact Hst|].
    pose proof (mm_gt_graph_lookup k a b st (k+1)%Z Hab Hat (Hq st Hst)) as Hb.
    assert (Heq : Z.gtb (k+1) k = true) by (apply Z.gtb_lt; lia).
    rewrite Heq in Hb. exact Hb.
  - exists sf. split; [exact Hsf|].
    pose proof (mm_gt_graph_lookup k a b sf 1%Z Hab Haf (Hq sf Hsf)) as Hb.
    assert (Heq : Z.gtb 1 k = false).
    { destruct (Z.gtb 1 k) eqn:Hgt; [apply Z.gtb_lt in Hgt; lia|reflexivity]. }
    rewrite Heq in Hb. exact Hb.
Qed.
