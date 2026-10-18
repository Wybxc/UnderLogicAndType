(** Complete declarative derivation of revised Figure 6(a). *)
From CaseStudy Require Import MayMustRevised MayMustBase MayMustPrimitives MayMustBoolCases
  MayMustTyping MayMustUnder MayMustAbsorption MayMustIndependentCases.
From ContextTyping Require Import Typing TypingRegular Subtyping BasicBindings SoundnessLam
  PrimOpConcreteContext NatCases ConstCases Weakening Soundness.
From Denotation Require Import Context TypeEquiv TypeEquivCore.
From Stdlib Require Import ZArith.

Lemma mm_int_top_var_typed Φ Γ x :
  wf_ctx_under ∅ Γ -> erase_ctx Γ !! x = Some (TBase TInt) ->
  has_context_type Φ ∅ Γ (tret (vfvar x)) (OInt (fun _ => True)).
Proof.
  intros HΓ Hx. eapply CT_CtxSub with (Γ2:=CtxBind x (OInt (fun _ => True))).
  - split; [exact HΓ|]. split; [apply int_pred_over_wf|apply TT_Ret,VT_FVar; exact Hx].
  - apply CT_Var. split; [split; [set_solver|apply int_pred_over_wf]|].
    split; [apply int_pred_over_wf|apply TT_Ret,VT_FVar,map_lookup_singleton].
  - split; [exact HΓ|]. split; [split; [set_solver|apply int_pred_over_wf]|]. split.
    + intros z Hz. rewrite (int_pred_fv true (fun _ => True)) in Hz.
      cbn [fv_tm fv_value] in Hz. assert (z=x) by (clear -Hz; set_solver). subst z.
      transitivity (Some (TBase TInt)); [exact Hx|symmetry; apply map_lookup_singleton].
    + intros m Hctx. exists m. split; [apply res_restrict_le|].
      apply int_bind_over_intro.
      * exact (ctx_denote_under_basic_singleton ∅ Γ x (TBase TInt) m HΓ Hx Hctx).
      * intros s Hs.
        destruct (ctx_denote_under_lookup_typed ∅ Γ x (TBase TInt) m s HΓ Hx Hctx Hs)
          as [v [Hv Hty]].
        destruct (basic_typing_int_canonical_form v Hty) as [z ->]. exists z. auto.
Qed.

Lemma mm_sub_base_top Γ τ b :
  wf_ctx_under ∅ Γ -> wf_context_ty_at 0 (dom (erase_ctx Γ)) τ -> erase_ty τ=TBase b ->
  sub_type_under ∅ Γ τ (CTOver b qual_top).
Proof.
  intros HΓ Hτ Hb. apply sub_type_under_intro;
    [exact HΓ|exact Hτ|apply qual_top_lvars_wf_at; lia|exact Hb|].
  intros e m He Hctx Hsource.
  assert (Hwf : context_typing_wf ∅ Γ e (CTOver b qual_top)).
  { split; [exact HΓ|]. split; [apply qual_top_lvars_wf_at; lia|]. change (tm_has_type (erase_ctx Γ) e (TBase b)). rewrite <- Hb. exact He. }
  unfold ty_denote_under,ty_denote. apply ty_denote_gas_over_top_from_zero.
  apply ty_denote_gas_zero_of_guard,ty_guard_relevant_of_static_full_total.
  - exact (context_typing_wf_denot_static_guard_full _ _ _ _ _ Hwf Hctx).
  - exact (ty_denote_under_total _ _ _ _ _ Hsource).
Qed.

Lemma mm_succ_top_typed Γ x :
  wf_ctx_under ∅ Γ -> erase_ctx Γ !! x = Some (TBase TInt) ->
  has_context_type concrete_Φ ∅ Γ (tprim op_int_plus1 (vfvar x)) (CTOver TInt qual_top).
Proof.
  intros HΓ Hx. eapply CT_Sub with
    (τ1:=CTOver TInt (expr_result_qual (tprim op_int_plus1 (vfvar x)) (LVBound 0))).
  - split; [exact HΓ|]. split; [apply qual_top_lvars_wf_at; lia|].
    eapply TT_Op; [reflexivity|apply VT_FVar; exact Hx].
  - exact (mm_prim_over_typed Γ op_int_plus1 x TInt TInt eq_refl HΓ Hx).
  - apply mm_sub_base_top; [exact HΓ| |reflexivity].
    exact (proj1 (mm_prim_graph_wf Γ op_int_plus1 x TInt TInt eq_refl Hx)).
Qed.

Lemma mm_a_branch_lookups g x y b flag :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  erase_ctx (mm_a_branch_ctx g x y b flag) !! g=Some (TArrow TInt TInt) /\
  erase_ctx (mm_a_branch_ctx g x y b flag) !! x=Some (TBase TInt) /\
  erase_ctx (mm_a_branch_ctx g x y b flag) !! b=Some (TBase TBool).
Proof.
  intros Hgx Hy Hb. repeat split.
  - repeat apply erase_ctx_comma_lookup_old. apply map_lookup_singleton.
  - apply erase_ctx_comma_lookup_old,erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅ _ x _ (mm_a_ctx_wf g x Hgx)).
  - exact (erase_ctx_comma_lookup_new_wf ∅ _ b _ (mm_a_branch_wf g x y b flag Hgx Hy Hb)).
Qed.

Lemma mm_a_call_typed g x y b :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  has_context_type concrete_Φ ∅ (mm_a_branch_ctx g x y b true)
    (tapp (vfvar g) (vfvar x)) (OInt (fun z => z<>0%Z)).
Proof.
  intros Hgx Hy Hb. pose proof (mm_a_branch_wf g x y b true Hgx Hy Hb) as HΓ.
  destruct (mm_a_branch_lookups g x y b true Hgx Hy Hb) as [Hg [Hx Hbl]].
  replace (OInt (fun z => z<>0%Z)) with (cty_open 0 x (OInt (fun z => z<>0%Z)))
    by (apply mm_closed_type_open; apply int_pred_over_wf).
  apply CT_AppFun with (τx:=OInt (fun _ => True)).
  - split; [exact HΓ|]. split.
    + rewrite mm_closed_type_open by apply int_pred_over_wf. apply int_pred_over_wf.
    + rewrite cty_open_preserves_erasure. eapply TT_App; apply VT_FVar; eassumption.
  - rewrite !(int_pred_fv true). cbn [fv_value]. clear -Hgx. set_solver.
  - apply typing_comma_prefix_wf; [exact HΓ|].
    apply typing_comma_prefix_wf; [exact (proj1 HΓ)|].
    apply typing_comma_prefix_wf; [apply mm_a_ctx_wf; exact Hgx|].
    apply CT_Var. split; [split; [set_solver|apply may_help_must_g_wf]|].
    split; [apply may_help_must_g_wf|apply TT_Ret,VT_FVar,map_lookup_singleton].
  - apply mm_int_top_var_typed; assumption.
Qed.

Definition mm_a_then g x :=
  tlete (tapp (vfvar g) (vfvar x)) (tprim op_int_plus1 (vbvar 0)).
Definition mm_a_match g x b :=
  tmatch (vfvar b) (mm_a_then g x) (tprim op_int_plus1 (vfvar x)).
Definition mm_a_body g x y :=
  tlete (tprim (op_int_gt 10) (vfvar y))
    (tmatch (vbvar 0) (mm_a_then g x) (tprim op_int_plus1 (vfvar x))).

Lemma mm_a_then_basic Δ g x :
  Δ !! g=Some (TArrow TInt TInt) -> Δ !! x=Some (TBase TInt) ->
  tm_has_type Δ (mm_a_then g x) (TBase TInt).
Proof.
  intros Hg Hx. apply TT_Let with (T1:=TBase TInt) (L:=∅).
  - eapply TT_App; apply VT_FVar; eassumption.
  - intros a _. change (tm_has_type (<[a:=TBase TInt]>Δ)
      (tprim op_int_plus1 (vfvar a)) (TBase TInt)).
    eapply TT_Op; [reflexivity|apply VT_FVar,map_lookup_insert].
Qed.

Lemma mm_a_match_basic Δ g x b :
  Δ !! g=Some (TArrow TInt TInt) -> Δ !! x=Some (TBase TInt) -> Δ !! b=Some (TBase TBool) ->
  tm_has_type Δ (mm_a_match g x b) (TBase TInt).
Proof.
  intros Hg Hx Hb. apply TT_Match.
  - apply VT_FVar. exact Hb.
  - apply mm_a_then_basic; assumption.
  - eapply TT_Op; [reflexivity|apply VT_FVar; exact Hx].
Qed.

Lemma mm_a_then_typed g x y b :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  has_context_type concrete_Φ ∅ (mm_a_branch_ctx g x y b true)
    (mm_a_then g x) (CTOver TInt qual_top).
Proof.
  intros Hgx Hy Hb. pose proof (mm_a_branch_wf g x y b true Hgx Hy Hb) as HΓ.
  destruct (mm_a_branch_lookups g x y b true Hgx Hy Hb) as [Hg [Hx Hbl]].
  apply CT_Let with (τ1:=OInt (fun z => z<>0%Z))
    (L:=ctx_dom (mm_a_branch_ctx g x y b true)).
  - split; [exact HΓ|]. split; [apply qual_top_lvars_wf_at; lia|apply mm_a_then_basic; assumption].
  - apply mm_a_call_typed; assumption.
  - intros a Ha. change (has_context_type concrete_Φ ∅
      (CtxComma (mm_a_branch_ctx g x y b true) (CtxBind a (OInt (fun z => z<>0%Z))))
      (tprim op_int_plus1 (vfvar a)) (CTOver TInt qual_top)).
    assert (Hnew : wf_ctx_under ∅ (CtxComma (mm_a_branch_ctx g x y b true)
      (CtxBind a (OInt (fun z => z<>0%Z)))))
      by (apply mm_wf_comma_bind; [exact HΓ|exact Ha|apply int_pred_over_wf]).
    apply mm_succ_top_typed; [exact Hnew|]. exact (erase_ctx_comma_lookup_new_wf ∅ _ a _ Hnew).
Qed.

Lemma mm_a_else_typed g x y b :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  has_context_type concrete_Φ ∅ (mm_a_branch_ctx g x y b false)
    (tprim op_int_plus1 (vfvar x)) (UInt (fun z => z=1%Z)).
Proof.
  intros Hgx Hy Hb. pose proof (mm_a_branch_wf g x y b false Hgx Hy Hb) as HΓ.
  destruct (mm_a_branch_lookups g x y b false Hgx Hy Hb) as [Hg [Hx Hbl]].
  apply mm_succ_under_typed; [exact HΓ|exact Hx|].
  intros m Hctx. pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as H1.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m H1) as H2.
  pose proof (mm_comma_closed_right ∅ _ x (UInt (fun z => z=0%Z)) m
    (int_pred_fv false _) H2) as Hxctx.
  exact (int_bind_under_covers x (fun z => z=0%Z) m 0 Hxctx eq_refl).
Qed.

Lemma mm_a_false_match_typed g x y b :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  has_context_type concrete_Φ ∅ (mm_a_branch_ctx g x y b false)
    (mm_a_match g x b) (UInt (fun z => z=1%Z)).
Proof.
  intros Hgx Hy Hb. pose proof (mm_a_branch_wf g x y b false Hgx Hy Hb) as HΓ.
  destruct (mm_a_branch_lookups g x y b false Hgx Hy Hb) as [Hg [Hx Hbl]].
  apply CT_MatchFalseOnly.
  - split; [exact HΓ|]. split; [apply int_pred_wf|apply mm_a_match_basic; assumption].
  - apply typing_var_right_wf. exact HΓ.
  - apply mm_a_else_typed; assumption.
Qed.

Lemma mm_a_both_match_typed g x y b :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  has_context_type concrete_Φ ∅
    (CtxSum (mm_a_branch_ctx g x y b true) (mm_a_branch_ctx g x y b false))
    (mm_a_match g x b) (UInt (fun z => z=1%Z)).
Proof.
  intros Hgx Hy Hb.
  assert (HΓ : wf_ctx_under ∅ (CtxSum (mm_a_branch_ctx g x y b true)
    (mm_a_branch_ctx g x y b false))).
  { split; [apply mm_a_branch_wf; assumption|]. split; [apply mm_a_branch_wf; assumption|]. split; reflexivity. }
  destruct (mm_a_branch_lookups g x y b true Hgx Hy Hb) as [Hg [Hx Hbl]].
  assert (Hbasic : tm_has_type (erase_ctx (CtxSum (mm_a_branch_ctx g x y b true)
    (mm_a_branch_ctx g x y b false))) (mm_a_match g x b) (TBase TInt)).
  { apply mm_a_match_basic; assumption. }
  eapply CT_Sub with (τ1:=CTSum (CTOver TInt qual_top) (UInt (fun z => z=1%Z))).
  - split; [exact HΓ|]. split; [apply int_pred_wf|exact Hbasic].
  - apply CT_MatchBoth.
    + split; [exact HΓ|]. split; [|exact Hbasic].
      split; [apply qual_top_lvars_wf_at; lia|]. split; [apply int_pred_wf|reflexivity].
    + apply typing_var_right_wf,mm_a_branch_wf; assumption.
    + apply typing_var_right_wf,mm_a_branch_wf; assumption.
    + apply mm_a_then_typed; assumption.
    + apply mm_a_else_typed; assumption.
  - apply mm_sum_under_absorb. exact HΓ.
Qed.

Lemma mm_a_body_basic Δ g x y :
  Δ !! g=Some (TArrow TInt TInt) -> Δ !! x=Some (TBase TInt) -> Δ !! y=Some (TBase TInt) ->
  tm_has_type Δ (mm_a_body g x y) (TBase TInt).
Proof.
  intros Hg Hx Hy. apply TT_Let with (T1:=TBase TBool) (L:={[g;x]}).
  - eapply TT_Op; [reflexivity|apply VT_FVar; exact Hy].
  - intros b Hb. change (tm_has_type (<[b:=TBase TBool]>Δ) (mm_a_match g x b) (TBase TInt)).
    apply mm_a_match_basic.
    + assert (Hbg : b<>g).
      { intros ->. apply Hb,elem_of_union_l,elem_of_singleton. reflexivity. }
      exact (mm_insert_lookup Δ b g (TBase TBool) (TArrow TInt TInt) Hbg Hg).
    + exact (mm_insert_lookup Δ b x (TBase TBool) (TBase TInt) ltac:(intros ->; apply Hb,elem_of_union_r,elem_of_singleton; reflexivity) Hx).
    + apply map_lookup_insert.
Qed.

Lemma mm_a_input_lookups g x y : g<>x -> y ∉ ({[g;x]} : aset) ->
  erase_ctx (mm_a_inputs g x y) !! g=Some (TArrow TInt TInt) /\
  erase_ctx (mm_a_inputs g x y) !! x=Some (TBase TInt) /\
  erase_ctx (mm_a_inputs g x y) !! y=Some (TBase TInt).
Proof.
  intros Hgx Hy. repeat split.
  - apply erase_ctx_comma_lookup_old,erase_ctx_comma_lookup_old,map_lookup_singleton.
  - apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅ _ x _ (mm_a_ctx_wf g x Hgx)).
  - apply mm_a_input_y; assumption.
Qed.

Lemma mm_a_body_typed g x y : g<>x -> y ∉ ({[g;x]} : aset) ->
  has_context_type concrete_Φ ∅ (mm_a_inputs g x y) (mm_a_body g x y)
    (UInt (fun z => z=1%Z)).
Proof.
  intros Hgx Hy. pose proof (mm_a_inputs_wf g x y Hgx Hy) as HΓ.
  destruct (mm_a_input_lookups g x y Hgx Hy) as [Hg [Hx Hyl]].
  apply CT_Let with (τ1:=mm_gt_ty 10 y) (L:={[g;x;y]}).
  - split; [exact HΓ|]. split; [apply int_pred_wf|apply mm_a_body_basic; assumption].
  - exact (mm_prim_over_typed _ (op_int_gt 10) y TInt TBool eq_refl HΓ Hyl).
  - intros b Hb. change (has_context_type concrete_Φ ∅ (mm_a_compare_ctx g x y b)
      (mm_a_match g x b) (UInt (fun z => z=1%Z))).
    pose proof (mm_a_compare_wf g x y b Hgx Hy Hb) as Hnew.
    eapply CT_CtxCases with (cases:=[mm_a_branch_ctx g x y b false;
      CtxSum (mm_a_branch_ctx g x y b true) (mm_a_branch_ctx g x y b false)]).
    + split; [exact Hnew|]. split; [apply int_pred_wf|].
      apply mm_a_match_basic.
      * apply erase_ctx_comma_lookup_old. exact Hg.
      * apply erase_ctx_comma_lookup_old. exact Hx.
      * exact (erase_ctx_comma_lookup_new_wf ∅ _ b _ Hnew).
    + intros Δ [<-|[<-|[]]]; reflexivity.
    + intros Δ [<-|[<-|[]]].
      * apply mm_a_false_match_typed; assumption.
      * apply mm_a_both_match_typed; assumption.
    + apply mm_a_cases; assumption.
Qed.

Definition mm_a_inner g x : value := vlam TInt
  (tlete (tprim (op_int_gt 10) (vbvar 0))
    (tmatch (vbvar 0) (mm_a_then g x) (tprim op_int_plus1 (vfvar x)))).

Lemma mm_a_inner_basic Δ g x :
  Δ !! g=Some (TArrow TInt TInt) -> Δ !! x=Some (TBase TInt) ->
  value_has_type Δ (mm_a_inner g x) (TArrow TInt TInt).
Proof.
  intros Hg Hx. apply VT_Lam with (L:={[g;x]}).
  intros y Hy. change (tm_has_type (<[y:=TBase TInt]>Δ) (mm_a_body g x y) (TBase TInt)).
  apply mm_a_body_basic.
  - exact (mm_insert_lookup Δ y g (TBase TInt) (TArrow TInt TInt)
      ltac:(intros ->; apply Hy,elem_of_union_l,elem_of_singleton; reflexivity) Hg).
  - exact (mm_insert_lookup Δ y x (TBase TInt) (TBase TInt)
      ltac:(intros ->; apply Hy,elem_of_union_r,elem_of_singleton; reflexivity) Hx).
  - apply map_lookup_insert.
Qed.

Lemma mm_a_inner_typed g x : g<>x ->
  has_context_type concrete_Φ ∅ (mm_a_ctx g x) (tret (mm_a_inner g x))
    (CTWand (UInt (fun z => (0<=z<=10)%Z)) (UInt (fun z => z=1%Z))).
Proof.
  intros Hgx. pose proof (mm_a_ctx_wf g x Hgx) as HΓ.
  apply CT_LamD with (τx:=UInt (fun z => (0<=z<=10)%Z)) (L:={[g;x]}).
  - split; [exact HΓ|]. split; [split; apply int_pred_wf|].
    apply TT_Ret,mm_a_inner_basic.
    + apply erase_ctx_comma_lookup_old,map_lookup_singleton.
    + exact (erase_ctx_comma_lookup_new_wf ∅ _ x _ HΓ).
  - intros y Hy. rewrite mm_closed_type_open by apply int_pred_wf.
    change (has_context_type concrete_Φ ∅ (mm_a_inputs g x y) (mm_a_body g x y)
      (UInt (fun z => z=1%Z))).
    apply mm_a_body_typed; assumption.
Qed.

Theorem may_help_must_context_typed g :
  has_context_type concrete_Φ ∅ (CtxBind g may_help_must_g_ty)
    (tret (may_help_must g)) may_help_must_ty.
Proof.
  unfold may_help_must_ty,may_help_must.
  apply CT_Lam with (τx:=UInt (fun z => z=0%Z)) (L:={[g]}).
  - split; [split; [set_solver|apply may_help_must_g_wf]|].
    split; [apply may_help_must_wf|].
    apply TT_Ret,may_help_must_basic,map_lookup_singleton.
  - intros x Hx. apply not_elem_of_singleton in Hx.
    rewrite mm_closed_type_open by (split; apply int_pred_wf).
    change (has_context_type concrete_Φ ∅ (mm_a_ctx g x) (tret (mm_a_inner g x))
      (CTWand (UInt (fun z => (0<=z<=10)%Z)) (UInt (fun z => z=1%Z)))).
    apply mm_a_inner_typed. congruence.
Qed.

Corollary may_help_must_context_sound g :
  ctx_denote_under ∅ (CtxBind g may_help_must_g_ty) ⊫
    ty_denote_under ∅ (CtxBind g may_help_must_g_ty)
      may_help_must_ty (tret (may_help_must g)).
Proof. apply concrete_Fundamental,may_help_must_context_typed. Qed.

Print Assumptions may_help_must_context_typed.
Print Assumptions may_help_must_context_sound.
