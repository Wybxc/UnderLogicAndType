(** Independence preserves the complete left projection when the right input
    is filtered. In particular no stability of ordinary arrows is assumed. *)
From CaseStudy Require Import MayMustRevised MayMustBase MayMustPrimitives
  MayMustBoolCases MayMustTyping MayMustWorlds.
From ContextTyping Require Import Typing TypingRegular Subtyping BasicBindings
  NatCases ConstCases PrimOpConcreteContext.
From Denotation Require Import Context TypeEquiv TypeEquivCore.
From ContextLogic Require Import FormulaConnectives.
From Stdlib Require Import ZArith Lia Classical_Prop.

Definition mm_cut y (s : StoreT) : Prop :=
  exists z, s !! y = Some (vint z) /\ (9 < z)%Z.

Lemma mm_cut_restrict y s X : y ∈ X ->
  mm_cut y s <-> mm_cut y (store_restrict s X).
Proof.
  intros Hy. unfold mm_cut.
  assert (Hlookup : (store_restrict s X : StoreT) !! y = s !! y).
  { change ((storeA_restrict s X : gmap atom value) !! y = s !! y).
    eapply eq_trans; [exact (storeA_restrict_lookup s X y)|].
    rewrite decide_True by exact Hy. reflexivity. }
  rewrite Hlookup. reflexivity.
Qed.

Lemma mm_erase_dom_subset Γ : dom (erase_ctx Γ) ⊆ ctx_dom Γ.
Proof.
  induction Γ; cbn [erase_ctx ctx_dom]; unfold store_union,store_empty;
    rewrite ?dom_empty_L,?dom_singleton_L,?dom_union_L; try set_solver.
  unfold store_singleton. rewrite dom_singleton_L. reflexivity.
Qed.

Lemma mm_ctx_formula_fv Σ Γ :
  formula_fv (ctx_denote_under Σ Γ) ⊆ dom (Σ : gmap atom ty) ∪ ctx_dom Γ ∪ ctx_fv Γ.
Proof.
  induction Γ in Σ |- *.
  all: cbn [ctx_denote_under]; rewrite formula_fv_and,formula_fv_basic_world_formula,
    lvars_fv_atom_env_to_lty_env_dom.
  - rewrite (formula_fv_true (V:=value)). cbn [ctx_fv ctx_dom erase_ctx].
    unfold store_union,store_empty. rewrite dom_union_L,storeA_restrict_dom,dom_empty_L. set_solver.
  - pose proof (ty_denote_gas_fv_subset (cty_depth τ)
      (atom_env_to_lty_env (<[x:=erase_ty τ]>(store_restrict Σ (ctx_fv (CtxBind x τ)))) )
      τ (tret (vfvar x))) as Hty.
    unfold ty_denote. cbn [ctx_fv ctx_dom erase_ctx fv_tm fv_value] in *.
    unfold store_union,store_empty,store_singleton. rewrite dom_union_L,storeA_restrict_dom,dom_singleton_L.
    set_solver.
  - rewrite formula_fv_and. specialize (IHΓ1 (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)))).
    specialize (IHΓ2 ((store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2))) ∪ erase_ctx Γ1)).
    pose proof (mm_erase_dom_subset Γ1). pose proof (mm_erase_dom_subset Γ2).
    cbn [ctx_fv ctx_dom erase_ctx] in *.
    unfold store_union in *. rewrite !dom_union_L,!storeA_restrict_dom in *.
    intros z Hz. specialize (IHΓ1 z). specialize (IHΓ2 z).
    specialize (H z). specialize (H0 z).
    set_unfold in IHΓ1. set_unfold in IHΓ2. set_unfold in H. set_unfold in H0. set_unfold in Hz. set_unfold. destruct (classic (z ∈ ctx_dom Γ1)); tauto.
  - rewrite formula_fv_star.
    specialize (IHΓ1 (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))).
    specialize (IHΓ2 (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))).
    pose proof (mm_erase_dom_subset Γ1). pose proof (mm_erase_dom_subset Γ2).
    cbn [ctx_fv ctx_dom erase_ctx] in *.
    unfold store_union in *. rewrite !dom_union_L,!storeA_restrict_dom in *. set_solver.
  - rewrite formula_fv_plus.
    specialize (IHΓ1 (store_restrict Σ (ctx_fv (CtxSum Γ1 Γ2)))).
    specialize (IHΓ2 (store_restrict Σ (ctx_fv (CtxSum Γ1 Γ2)))).
    pose proof (mm_erase_dom_subset Γ1). pose proof (mm_erase_dom_subset Γ2).
    cbn [ctx_fv ctx_dom erase_ctx] in *.
    unfold store_union in *. rewrite !dom_union_L,!storeA_restrict_dom in *. set_solver.
Qed.

Lemma mm_union_lookup_right (s t : StoreT) y :
  storeA_compat s t -> y ∈ dom (t : StoreT) -> (s ∪ t) !! y = t !! y.
Proof.
  intros Hcompat Hy. change (y ∈ dom (t : gmap atom value)) in Hy.
  apply elem_of_dom in Hy as [v Hv].
  change ((s ∪ t : gmap atom value) !! y = t !! y).
  transitivity (Some v); [|symmetry; exact Hv].
  apply map_lookup_union_Some_raw. destruct (s !! y) as [w|] eqn:Hw.
  - left. assert (w=v) by (eapply Hcompat; eassumption). subst w. exact Hw.
  - right. auto.

Qed.

Lemma mm_cut_product y (c d : WfWorldT) (Hcd : world_compat c d) :
  y ∈ world_dom (d : WorldT) ->
  forall s t, (c : WorldT) s -> (d : WorldT) t ->
    mm_cut y (s ∪ t) <-> mm_cut y t.
Proof.
  intros Hyd s t Hs Ht. unfold mm_cut.
  assert (Hdom : y ∈ dom (t : StoreT)).
  { pose proof (wfworld_store_dom d t Ht) as HD.
    change (dom (t : StoreT) = world_dom (d : WorldT)) in HD.
    rewrite HD. exact Hyd. }
  pose proof (mm_union_lookup_right s t y (Hcd s t Hs Ht) Hdom) as Hlook.
  split; intros [z [Hz HP]]; exists z; split; [|exact HP| |exact HP].
  - exact (eq_trans (eq_sym Hlook) Hz).
  - exact (eq_trans Hlook Hz).

Qed.

Lemma mm_cut_keeps_left (c d m : WfWorldT) y Hcd
    (HP : exists s, (m : WorldT) s /\ mm_cut y s) :
  y ∈ world_dom (d : WorldT) -> res_product c d Hcd ⊑ m ->
  c ⊑ select_world m (mm_cut y) HP.
Proof.
  intros Hyd Hle.
  set (p := res_product c d Hcd).
  assert (Hyp : y ∈ world_dom (p : WorldT)).
  { change (y ∈ world_dom (c : WorldT) ∪ world_dom (d : WorldT)). set_solver. }
  assert (Hlocal : forall s, mm_cut y s <-> mm_cut y (store_restrict s (world_dom (p : WorldT)))).
  { intros s. apply mm_cut_restrict. exact Hyp. }
  assert (Hprod : exists s, (p : WorldT) s /\ mm_cut y s).
  { destruct HP as [s [Hs HPs]].
    exists (store_restrict s (world_dom (p : WorldT))). split.
    - rewrite <- (res_restrict_eq_of_le p m Hle).
      exists s. split; [exact Hs|].
      f_equal. rewrite res_restrict_dom.
      pose proof (raw_le_dom _ _ Hle). set_solver.
    - exact (proj1 (Hlocal s) HPs). }
  assert (Hd : exists t, (d : WorldT) t /\ mm_cut y t).
  { destruct Hprod as [s [[a [b [Ha [Hb [Hab ->]]]]] HPs]].
    exists b. split; [exact Hb|]. exact (proj1 (mm_cut_product y c d Hcd Hyd a b Ha Hb) HPs). }
  exact (select_world_extension_keeps_left c d m (mm_cut y) Hcd Hd Hprod HP
    Hle Hlocal (mm_cut_product y c d Hcd Hyd)).
Qed.

Lemma mm_notcut_keeps_left (c d m : WfWorldT) y Hcd
    (HP : exists s, (m : WorldT) s /\ ~mm_cut y s) :
  y ∈ world_dom (d : WorldT) -> res_product c d Hcd ⊑ m ->
  c ⊑ select_world m (fun s => ~mm_cut y s) HP.
Proof.
  intros Hyd Hle. set (p := res_product c d Hcd).
  assert (Hyp : y ∈ world_dom (p : WorldT)).
  { change (y ∈ world_dom (c : WorldT) ∪ world_dom (d : WorldT)). set_solver. }
  assert (Hlocal : forall s, (~mm_cut y s) <-> ~mm_cut y (store_restrict s (world_dom (p : WorldT)))).
  { intros s. rewrite <- mm_cut_restrict by exact Hyp. reflexivity. }
  assert (Hprod : exists s, (p : WorldT) s /\ ~mm_cut y s).
  { destruct HP as [s [Hs HPs]]. exists (store_restrict s (world_dom (p : WorldT))). split.
    - rewrite <- (res_restrict_eq_of_le p m Hle). exists s. split; [exact Hs|].
      f_equal. rewrite res_restrict_dom. pose proof (raw_le_dom _ _ Hle). set_solver.
    - exact (proj1 (Hlocal s) HPs). }
  assert (Hright : forall a b, (c : WorldT) a -> (d : WorldT) b ->
    (~mm_cut y (a∪b)) <-> ~mm_cut y b).
  { intros a b Ha Hb. rewrite (mm_cut_product y c d Hcd Hyd a b Ha Hb). reflexivity. }
  assert (Hd : exists t, (d : WorldT) t /\ ~mm_cut y t).
  { destruct Hprod as [s [[a [b [Ha [Hb [Hab ->]]]]] HPs]].
    exists b. split; [exact Hb|]. exact (proj1 (Hright a b Ha Hb) HPs). }
  exact (select_world_extension_keeps_left c d m (fun s => ~mm_cut y s) Hcd Hd Hprod HP
    Hle Hlocal Hright).
Qed.

Definition mm_a_ctx g x := CtxComma (CtxBind g may_help_must_g_ty)
  (CtxBind x (UInt (fun z => z=0%Z))).
Definition mm_a_inputs g x y := CtxStar (mm_a_ctx g x)
  (CtxBind y (UInt (fun z => (0<=z<=10)%Z))).
Definition mm_a_compare_ctx g x y b := CtxComma (mm_a_inputs g x y)
  (CtxBind b (mm_gt_ty 9 y)).
Definition mm_a_branch_ctx g x y b flag :=
  CtxComma (CtxComma (mm_a_ctx g x) (CtxBind y (CTOver TInt qual_top)))
    (CtxBind b (bool_precise_ty flag)).

Lemma mm_a_ctx_wf g x : g <> x -> wf_ctx_under ∅ (mm_a_ctx g x).
Proof.
  intros Hgx. apply mm_wf_comma_bind.
  - split; [set_solver|apply may_help_must_g_wf].
  - cbn [ctx_dom]. clear -Hgx. set_solver.
  - apply int_pred_wf.
Qed.

Lemma mm_a_inputs_wf g x y : g<>x -> y ∉ ({[g;x]} : aset) ->
  wf_ctx_under ∅ (mm_a_inputs g x y).
Proof.
  intros Hgx Hy. split; [apply mm_a_ctx_wf; exact Hgx|]. split.
  - split; [set_solver|apply int_pred_wf].
  - cbn [ctx_dom mm_a_ctx]. clear -Hy. set_solver.
Qed.

Lemma mm_a_branch_wf g x y b flag : g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  wf_ctx_under ∅ (mm_a_branch_ctx g x y b flag).
Proof.
  intros Hgx Hy Hb. apply mm_wf_comma_bind.
  - apply mm_wf_comma_bind; [apply mm_a_ctx_wf; exact Hgx| |apply qual_top_lvars_wf_at; lia].
    cbn [mm_a_ctx ctx_dom]. clear -Hy. set_solver.
  - cbn [ctx_dom mm_a_ctx]. clear -Hb. set_solver.
  - apply const_precise_wf.
Qed.

Lemma mm_comma_closed_intro Γ x τ (m : WfWorldT) :
  wf_ctx_under ∅ Γ -> fv_cty τ=∅ ->
  m ⊨ ctx_denote_under ∅ Γ -> m ⊨ ctx_denote_under ∅ (CtxBind x τ) ->
  m ⊨ ctx_denote_under ∅ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros HΓ Hclosed Hl Hr. apply ctx_denote_under_comma_intro; [exact HΓ|exact Hl|].
  rewrite ctx_denote_closed_env; [exact Hr|]. cbn [ctx_fv]. rewrite Hclosed. reflexivity.
Qed.

Lemma mm_a_input_y g x y : g<>x -> y ∉ ({[g;x]} : aset) ->
  erase_ctx (mm_a_inputs g x y) !! y = Some (TBase TInt).
Proof.
  intros Hgx Hy. change (erase_ctx (CtxComma (mm_a_ctx g x)
    (CtxBind y (UInt (fun z => (0<=z<=10)%Z)))) !! y = Some (TBase TInt)).
  apply erase_ctx_comma_lookup_new_wf with (Σ:=∅),mm_wf_comma_bind.
  - apply mm_a_ctx_wf. exact Hgx.
  - cbn [mm_a_ctx ctx_dom]. clear -Hy. set_solver.
  - apply int_pred_wf.
Qed.

Lemma mm_a_compare_wf g x y b : g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  wf_ctx_under ∅ (mm_a_compare_ctx g x y b).
Proof.
  intros Hgx Hy Hb. apply mm_wf_comma_bind.
  - apply mm_a_inputs_wf; assumption.
  - cbn [mm_a_inputs mm_a_ctx ctx_dom]. clear -Hb. set_solver.
  - exact (proj1 (mm_prim_graph_wf (mm_a_inputs g x y) (op_int_gt 9) y TInt TBool
      eq_refl (mm_a_input_y g x y Hgx Hy))).
Qed.

Lemma mm_a_branch_denote g x y b flag (m n : WfWorldT) :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  m ⊨ ctx_denote_under ∅ (mm_a_compare_ctx g x y b) ->
  res_subset n m -> n ⊨ ctx_denote_under ∅ (mm_a_ctx g x) ->
  (forall s, (n : WorldT) s -> s !! b = Some (vconst (cbool flag))) ->
  n ⊨ ctx_denote_under ∅ (mm_a_branch_ctx g x y b flag).
Proof.
  intros Hgx Hy Hb Hctx Hsub Hleft Hflag.
  pose proof (mm_a_compare_wf g x y b Hgx Hy Hb) as Hwf.
  pose proof (mm_a_input_y g x y Hgx Hy) as Hyl.
  assert (Hylookup : erase_ctx (mm_a_compare_ctx g x y b) !! y = Some (TBase TInt))
    by (apply erase_ctx_comma_lookup_old; exact Hyl).
  assert (Hblookup : erase_ctx (mm_a_compare_ctx g x y b) !! b = Some (TBase TBool))
    by exact (erase_ctx_comma_lookup_new_wf ∅ _ b _ Hwf).
  apply mm_comma_closed_intro.
  - apply mm_wf_comma_bind; [apply mm_a_ctx_wf; exact Hgx| |apply qual_top_lvars_wf_at; lia].
    cbn [mm_a_ctx ctx_dom]. clear -Hy. set_solver.
  - apply const_precise_fv.
  - apply mm_comma_closed_intro; [apply mm_a_ctx_wf; exact Hgx| |exact Hleft|].
    + pose proof (basic_context_ty_fv_subset ∅ _ (over_top_basic TInt)). set_solver.
    + apply over_top_bind_denote_from_basic_world.
      eapply basic_world_formula_res_subset; [exact Hsub|].
      exact (ctx_denote_under_basic_singleton ∅ _ y (TBase TInt) m Hwf Hylookup Hctx).
  - apply const_bind_denote_from_basic_world; [|exact Hflag].
    eapply basic_world_formula_res_subset; [exact Hsub|].
    exact (ctx_denote_under_basic_singleton ∅ _ b (TBase TBool) m Hwf Hblookup Hctx).
Qed.

Lemma mm_a_branch_scope g x y b flag (m : WfWorldT) :
  g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  m ⊨ ctx_denote_under ∅ (mm_a_compare_ctx g x y b) ->
  formula_scoped_in_world m (ctx_denote_under ∅ (mm_a_branch_ctx g x y b flag)).
Proof.
  intros Hgx Hy Hb Hctx.
  pose proof (mm_ctx_formula_fv ∅ (mm_a_branch_ctx g x y b flag)) as Hfv.
  pose proof (basic_ctx_fv_subset ∅ _ (mm_a_branch_wf g x y b flag Hgx Hy Hb)) as Hclosed.
  pose proof (basic_ctx_erase_dom ∅ _ (mm_a_compare_wf g x y b Hgx Hy Hb)) as HD.
  pose proof (ctx_denote_under_basic_world ∅ _ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset _ m Hworld) as Hscope.
  pose proof (ctx_erasure_under_erase_ctx_dom_subset ∅ (mm_a_compare_ctx g x y b)).
  assert (Hempty : ctx_fv (mm_a_branch_ctx g x y b flag) = ∅) by (clear -Hclosed; set_solver).
  rewrite Hempty,dom_empty_L in Hfv.
  unfold formula_scoped_in_world. intros z Hz. apply Hscope,H.
  rewrite HD. change (z ∈ ctx_dom (mm_a_branch_ctx g x y b flag)).
  specialize (Hfv z Hz). clear -Hfv. set_solver.

Qed.

Lemma mm_a_cases g x y b : g<>x -> y ∉ ({[g;x]} : aset) -> b ∉ ({[g;x;y]} : aset) ->
  ctx_denote_under ∅ (mm_a_compare_ctx g x y b) ⊫
  ctx_cases_denote ∅ [mm_a_branch_ctx g x y b false;
    CtxSum (mm_a_branch_ctx g x y b true) (mm_a_branch_ctx g x y b false)].
Proof.
  intros Hgx Hy Hb m Hctx.
  pose proof (mm_a_compare_wf g x y b Hgx Hy Hb) as Hwf.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hinputs.
  destruct (ctx_denote_under_star_elim ∅ _ _ m Hinputs) as [c [d [Hcd [Hle [Hc Hd]]]]].
  assert (Hyd : y ∈ world_dom (d : WorldT)).
  { pose proof (ctx_denote_under_basic_singleton ∅ (CtxBind y (UInt (fun z => (0<=z<=10)%Z))) y (TBase TInt) d
      ltac:(split; [set_solver|apply int_pred_wf]) ltac:(apply map_lookup_singleton) Hd) as Hworld.
    apply basic_world_formula_models_iff in Hworld as [_ [HD _]].
    apply HD. rewrite lvars_fv_atom_env_to_lty_env_dom.
    apply elem_of_dom. exists (TBase TInt). apply map_lookup_singleton. }
  assert (HCm : m ⊨ ctx_denote_under ∅ (mm_a_ctx g x)).
  { eapply res_models_kripke; [|exact Hc]. etransitivity; [apply res_product_le_l|exact Hle]. }
  assert (HYm : m ⊨ ctx_denote_under ∅ (CtxBind y (UInt (fun z => (0<=z<=10)%Z)))).
  { eapply res_models_kripke; [|exact Hd]. etransitivity; [apply res_product_le_r|exact Hle]. }
  destruct (int_bind_under_covers y (fun z => (0<=z<=10)%Z) m 0 HYm ltac:(cbn beta; lia))
    as [s0 [Hs0 Hy0]].
  assert (Hfalse : exists s, (m : WorldT) s /\ ~mm_cut y s).
  { exists s0. split; [exact Hs0|]. intros [z [Hz Hgt]].
    pose proof (eq_trans (eq_sym Hy0) Hz) as Heq. unfold vint in Heq. injection Heq as <-. lia. }
  assert (Hgraph : forall s, (m : WorldT) s ->
    qualifier_holds_store (qual_open_atom 0 b (typed_result_qual TBool
      (expr_result_qual (tprim (op_int_gt 9) (vfvar y)) (LVBound 0)))) s).
  { apply (mm_comma_over_store ∅ (mm_a_inputs g x y) b TBool _ m); [|exact Hctx].
    unfold qual_dom,expr_result_qual.
    cbn [qual_vars qual_lvars tm_lvars tm_lvars_at value_lvars_at bvar_lvars_at].
    rewrite lvars_fv_union,lvars_fv_singleton_free,lvars_fv_singleton_bound. clear -Hb. set_solver. }
  assert (Hflags : forall s, (m : WorldT) s ->
    (mm_cut y s -> s !! b = Some (vconst (cbool true))) /\
    (~mm_cut y s -> s !! b = Some (vconst (cbool false)))).
  { intros s Hs.
    destruct (ctx_denote_under_lookup_typed ∅ _ y (TBase TInt) m s Hwf
      (erase_ctx_comma_lookup_old _ _ _ _ _ (mm_a_input_y g x y Hgx Hy)) Hctx Hs)
      as [v [Hvy Hty]].
    destruct (basic_typing_int_canonical_form v Hty) as [z ->].
    pose proof (mm_gt_graph_lookup 9 y b s z ltac:(clear -Hb; set_solver) Hvy (Hgraph s Hs)) as Hvb.
    split.
    - intros [z' [Hz Hgt]].
      pose proof (eq_trans (eq_sym Hvy) Hz) as Heq. injection Heq as <-.
      rewrite (proj2 (Z.gtb_lt _ _) Hgt) in Hvb. exact Hvb.
    - intros Hnot. assert (Hgt : Z.gtb z 9=false).
      { destruct (Z.gtb z 9) eqn:Hz; [|reflexivity]. exfalso. apply Hnot.
        exists z. split; [exact Hvy|apply Z.gtb_lt; exact Hz]. }
      rewrite Hgt in Hvb. exact Hvb. }
  assert (HFscope := mm_a_branch_scope g x y b false m Hgx Hy Hb Hctx).
  assert (HTscope := mm_a_branch_scope g x y b true m Hgx Hy Hb Hctx).
  assert (HSscope : formula_scoped_in_world m (ctx_denote_under ∅
    (CtxSum (mm_a_branch_ctx g x y b true) (mm_a_branch_ctx g x y b false)))).
  { pose proof (mm_ctx_formula_fv ∅ (CtxSum (mm_a_branch_ctx g x y b true)
      (mm_a_branch_ctx g x y b false))) as Hfv.
    assert (Hwfsum : wf_ctx_under ∅ (CtxSum (mm_a_branch_ctx g x y b true)
      (mm_a_branch_ctx g x y b false))).
    { split; [apply mm_a_branch_wf; assumption|]. split; [apply mm_a_branch_wf; assumption|].
      split; reflexivity. }
    pose proof (basic_ctx_fv_subset ∅ _ Hwfsum) as HC.
    assert (Hempty : ctx_fv (CtxSum (mm_a_branch_ctx g x y b true)
      (mm_a_branch_ctx g x y b false)) = ∅) by (clear -HC; set_solver).
    rewrite Hempty,dom_empty_L in Hfv.
    pose proof (basic_ctx_erase_dom ∅ _ Hwf) as HD.
    pose proof (basic_world_formula_atom_env_dom_subset _ m
      (ctx_denote_under_basic_world ∅ _ m Hctx)) as HW.
    pose proof (ctx_erasure_under_erase_ctx_dom_subset ∅ (mm_a_compare_ctx g x y b)).
    unfold formula_scoped_in_world. intros z Hz. apply HW,H. rewrite HD.
    change (z ∈ ctx_dom (mm_a_branch_ctx g x y b true)).
    specialize (Hfv z Hz). change (z ∈ ∅ ∪
      (ctx_dom (mm_a_branch_ctx g x y b true) ∪ ctx_dom (mm_a_branch_ctx g x y b true)) ∪ ∅) in Hfv.
    clear -Hfv. set_solver. }

  cbn [ctx_cases_denote].
  destruct (classic (exists s, (m : WorldT) s /\ mm_cut y s)) as [Htrue|Hno].
  - set (mt := select_world m (mm_cut y) Htrue).
    set (mf := select_world m (fun s => ~mm_cut y s) Hfalse).
    assert (HT : mt ⊨ ctx_denote_under ∅ (mm_a_branch_ctx g x y b true)).
    { apply (mm_a_branch_denote g x y b true m mt Hgx Hy Hb Hctx (select_world_subset _ _ _)).
      - eapply res_models_kripke; [exact (mm_cut_keeps_left c d m y Hcd Htrue Hyd Hle)|exact Hc].
      - intros s [Hs HP]. exact (proj1 (Hflags s Hs) HP). }
    assert (HF : mf ⊨ ctx_denote_under ∅ (mm_a_branch_ctx g x y b false)).
    { apply (mm_a_branch_denote g x y b false m mf Hgx Hy Hb Hctx (select_world_subset _ _ _)).
      - eapply res_models_kripke; [exact (mm_notcut_keeps_left c d m y Hcd Hfalse Hyd Hle)|exact Hc].
      - intros s [Hs HP]. exact (proj2 (Hflags s Hs) HP). }
    assert (HS : m ⊨ ctx_denote_under ∅ (CtxSum (mm_a_branch_ctx g x y b true)
      (mm_a_branch_ctx g x y b false))).
    { destruct (select_world_partition m (mm_cut y) Htrue Hfalse) as [Hdef Heq].
      cbn [ctx_denote_under]. apply res_models_and_iff. split.
      - change (m ⊨ basic_world_formula (atom_env_to_lty_env
          (ctx_erasure_under ∅ (CtxSum (mm_a_branch_ctx g x y b true) (mm_a_branch_ctx g x y b false))))).
        change (ctx_erasure_under ∅ (CtxSum (mm_a_branch_ctx g x y b true) (mm_a_branch_ctx g x y b false)))
          with (ctx_erasure_under ∅ (mm_a_branch_ctx g x y b true)).
        assert (HE : ctx_erasure_under ∅ (mm_a_branch_ctx g x y b true) =
          ctx_erasure_under ∅ (mm_a_compare_ctx g x y b)).
        { unfold ctx_erasure_under. change
            ((storeA_restrict (∅ : gmap atom ty) (ctx_fv (mm_a_branch_ctx g x y b true))) ∪
              erase_ctx (mm_a_branch_ctx g x y b true) =
             (storeA_restrict (∅ : gmap atom ty) (ctx_fv (mm_a_compare_ctx g x y b))) ∪
              erase_ctx (mm_a_compare_ctx g x y b)).
          unfold store_empty. rewrite !storeA_restrict_empty. reflexivity. }
        rewrite HE. exact (ctx_denote_under_basic_world ∅ _ m Hctx).

      - eapply res_models_plus_intro with (m1:=mt) (m2:=mf) (Hdef:=Hdef).
        + unfold mt,mf. rewrite Heq. reflexivity.
        + rewrite ctx_denote_closed_env; [exact HT|].
          pose proof (basic_ctx_fv_subset ∅ _ (mm_a_branch_wf g x y b true Hgx Hy Hb)) as HC. clear -HC. set_solver.
        + rewrite ctx_denote_closed_env; [exact HF|].
          pose proof (basic_ctx_fv_subset ∅ _ (mm_a_branch_wf g x y b false Hgx Hy Hb)) as HC. clear -HC. set_solver. }
    apply res_models_or_intro_r_from_model; [exact HFscope|].
    apply res_models_or_intro_l_from_model; [exact HS|]. rewrite (formula_fv_false (V:=value)). apply empty_subseteq.
  - apply res_models_or_intro_l_from_model.
    + apply (mm_a_branch_denote g x y b false m m Hgx Hy Hb Hctx).
      * split; [reflexivity|auto].
      * exact HCm.
      * intros s Hs. apply (proj2 (Hflags s Hs)). intros HP. apply Hno. eauto.
    + rewrite formula_fv_or,(formula_fv_false (V:=value)).
      unfold formula_scoped_in_world in HSscope. clear -HSscope. set_solver.
Qed.
