(** Existential coverage consequences of existing T-Sub/T-AppOp. *)
From CaseStudy Require Import MayMustRevised MayMustBase MayMustPrimitives MayMustTyping.
From ContextTyping Require Import Typing TypingRegular Subtyping BasicBindings SoundnessLam PrimOpConcreteContext.
From Denotation Require Import Context TypeDenoteRegular TypeEquivCore TypeEquiv
  BaseCoverage ConditionalCoverage ResultQualifier QualifierStore.
From ContextBasicDenotation Require Import TermOpen TermEval.
From CoreLang Require Import OperationalProps.
From Stdlib Require Import ZArith.

Lemma mm_sub_under_singleton Γ φ z :
  wf_ctx_under ∅ Γ -> wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTUnder TInt φ) ->
  (forall (m : WfWorldT) y, m ⊨ ctx_denote_under ∅ Γ ->
    y ∉ world_dom (m : WorldT) ∪ qual_dom φ ->
    exists s, (m : WorldT) s /\
      qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TInt φ))
        (<[y:=vint z]> s)) ->
  sub_type_under ∅ Γ (CTUnder TInt φ) (UInt (fun n => n = z)).
Proof.
  intros HΓ Hφ Hwitness.
  apply sub_type_under_intro; [exact HΓ|exact Hφ|apply int_pred_wf|reflexivity|].
  intros e m He Hctx Hsource.
  assert (Hwf : context_typing_wf ∅ Γ e (UInt (fun n => n = z))).
  { split; [exact HΓ|]. split; [apply int_pred_wf|exact He]. }
  assert (Hzero : m ⊨ ty_denote_gas 0 (atom_env_to_lty_env (erase_ctx Γ))
      (UInt (fun n => n = z)) e).
  { apply ty_denote_gas_zero_of_guard. apply ty_guard_relevant_of_static_full_total.
    - exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx).
    - exact (ty_denote_under_total _ _ _ _ _ Hsource). }
  unfold ty_denote_under,ty_denote.
  apply (under_denote_intro_store_coverage 1 _ TInt (int_pred (fun n => n=z)) e m
    (world_dom (m : WorldT) ∪ qual_dom φ)).
  - exact (basic_context_ty_lc ∅ _ (int_pred_wf 0 ∅ _)).
  - exact Hzero.
  - intros y Hy s Hs. exists (<[y:=vint z]> s). split.
    + rewrite int_pred_typed,int_pred_open_store. exists z. split; [apply map_lookup_insert|reflexivity].
    + rewrite int_pred_dom,!storeA_restrict_empty_set. reflexivity.
  - intros y Hy s t Hs Hproj Hq.
    rewrite int_pred_typed,int_pred_open_store in Hq.
    destruct Hq as [n [Hty ->]].
    destruct (Hwitness m y Hctx Hy) as [s0 [Hs0 Hφ0]].
    pose proof (under_denote_elim_store_coverage 0
      (atom_env_to_lty_env (erase_ctx Γ)) TInt φ e m y
      (atom_store_to_lvar_store_closed _) (context_typing_wf_lc_tm _ _ _ _ Hwf)
      (basic_context_ty_lc _ _ Hφ) Hsource Hy) as [_ Hcover].
    destruct (Hcover s0 (<[y:=vint z]>s0) Hs0
      ltac:(apply storeA_restrict_insert_notin; clear -Hy; set_solver) Hφ0)
      as [s' [v [Hs' [_ [Hyv Heval]]]]].
    assert (Hveq : v = vint z).
    { pose proof (eq_trans (eq_sym Hyv)
        (map_lookup_insert s0 y (vint z))) as Heq. now injection Heq. }
    subst v. exists s', (vint z). split; [exact Hs'|]. split.
    + rewrite int_pred_dom,!storeA_restrict_empty_set. reflexivity.
    + auto.
Qed.

Lemma mm_expr_qual_store_intro e y (s : StoreT) v :
  lc_tm e -> y ∉ fv_tm e -> fv_tm e ⊆ dom (s : StoreT) ->
  s !! y = Some v -> tm_eval_in_store s e v ->
  qualifier_holds_store (expr_result_qual e (LVFree y)) s.
Proof.
  intros Hlc Hyfresh Hscope Hy Heval.
  assert (Hlcvars : lc_lvars (tm_lvars e ∪ {[LVFree y]})).
  { intros u Hu. apply elem_of_union in Hu as [Hu|Hu].
    - exact (tm_lvars_lc e Hlc u Hu).
    - apply elem_of_singleton in Hu as ->. exact I. }
  assert (Hfv : lvars_fv (tm_lvars e ∪ {[LVFree y]}) ⊆ dom (s : StoreT)).
  { rewrite lvars_fv_union,tm_lvars_fv,lvars_fv_singleton_free.
    assert (y ∈ dom (s : StoreT)).
    { change (y ∈ dom (s : gmap atom value)). apply elem_of_dom; eauto. }
    clear -H Hscope. set_solver. }
  exists Hlcvars,Hfv. split.
  - intros Hin. apply Hyfresh. rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hin.
  - exists v. split.
    + unfold lstore_on_lift_store. cbn [lso_store storeAO_store].
      apply storeA_restrict_lookup_some_2.
      * rewrite lstore_lift_free_lookup_free. exact Hy.
      * apply elem_of_union_r,elem_of_singleton. reflexivity.
    + unfold lstore_on_lift_store. cbn [lso_store storeAO_store].
      apply (proj2 (expr_eval_in_store_restrict_lvars e (lstore_lift_free s)
        (tm_lvars e ∪ {[LVFree y]}) v ltac:(set_solver))). exact Heval.
Qed.

Lemma mm_succ_under_typed Γ x :
  wf_ctx_under ∅ Γ -> erase_ctx Γ !! x = Some (TBase TInt) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ ->
    exists s, (m : WorldT) s /\ s !! x = Some (vint 0)) ->
  has_context_type concrete_Φ ∅ Γ (tprim op_int_plus1 (vfvar x)) (UInt (fun z => z=1%Z)).
Proof.
  intros HΓ Hx Hcover.
  pose proof (mm_prim_graph_wf Γ op_int_plus1 x TInt TInt eq_refl Hx) as Hgraph.
  eapply CT_Sub with
    (τ1:=CTUnder TInt (expr_result_qual (tprim op_int_plus1 (vfvar x)) (LVBound 0))).
  - split; [exact HΓ|]. split; [apply int_pred_wf|].
    eapply TT_Op; [reflexivity|apply VT_FVar; exact Hx].
  - apply typing_inter_r with
      (τ1:=CTOver TInt (expr_result_qual (tprim op_int_plus1 (vfvar x)) (LVBound 0))).
    exact (mm_prim_graph_typed Γ op_int_plus1 x TInt TInt eq_refl HΓ Hx).
  - apply mm_sub_under_singleton; [exact HΓ|exact (proj1 (proj2 Hgraph))|].
    intros m y Hctx Hy. destruct (Hcover m Hctx) as [s [Hs Hsx]].
    exists s. split; [exact Hs|].
    pose proof (PrimOpConcreteContext.typed_result_qual_prim_fvar_eq op_int_plus1 x) as Heq.
    change (typed_result_qual TInt
      (expr_result_qual (tprim op_int_plus1 (vfvar x)) (LVBound 0)) =
      expr_result_qual (tprim op_int_plus1 (vfvar x)) (LVBound 0)) in Heq.
    rewrite Heq.
    assert (Hscope : x ∈ world_dom (m : WorldT)).
    { pose proof (ctx_denote_under_basic_singleton ∅ Γ x (TBase TInt) m HΓ Hx Hctx) as Hworld.
      apply basic_world_formula_models_iff in Hworld as [_ [HD _]].
      apply HD. rewrite lvars_fv_atom_env_to_lty_env_dom.
      apply elem_of_dom. exists (TBase TInt). apply map_lookup_singleton. }
    assert (Hyx : y <> x) by (clear -Hy Hscope; set_solver).
    assert (Hlc : lc_tm (tprim op_int_plus1 (vfvar x))) by (apply LC_op,LC_fvar).
    rewrite (opened_expr_result_qual _ y Hlc ltac:(cbn [fv_tm fv_value]; clear -Hyx; set_solver)).
    apply mm_expr_qual_store_intro with (v:=vint 1); [exact Hlc| | |apply map_lookup_insert|].
    + cbn [fv_tm fv_value]. clear -Hyx. set_solver.
    + cbn [fv_tm fv_value]. rewrite store_insert_dom.
      pose proof (wfworld_store_dom m s Hs) as HD.
      change (dom (s : StoreT) = world_dom (m : WorldT)) in HD.
      rewrite HD. clear -Hscope. set_solver.
    + unfold tm_eval_in_store,expr_eval_in_store.
      assert (Hlookup : (<[y:=vint 1]>s : StoreT) !! x = Some (vint 0)).
      { exact (eq_trans (store_insert_lookup_ne s y x (vint 1) Hyx) Hsx). }
      rewrite (mm_instantiate_prim_var _ op_int_plus1 x (cint 0) Hlookup).
      apply Steps_step with (e2:=tret (vint 1)).
      * apply Step_head,HS_Op; [apply Prim_int_plus1|apply LC_op,LC_const].
      * apply Steps_refl,LC_ret,LC_const.
Qed.
