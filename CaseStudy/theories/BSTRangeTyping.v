(** The original two-argument range application, including its dependent
    interval result and the local constant-argument wrapper. *)
From CaseStudy Require Import CaseTypes BSTGenerator BSTContext BSTGeneratorTyping
  BSTNodeTypes BSTPositiveContext BSTRecursiveSupport NatArithmetic
  NatArithmeticStages NatArithmeticUnfolding ArithmeticProofTools.
From Denotation Require Import Context ResultQualifier QualifierStore.
From ContextTyping Require Import Typing TypingRegular BasicBindings ConstCases
  Subtyping OverConsequence FixedParameters Weakening NatCases.

Definition bst_lvar_value (z : logic_var) : value :=
  match z with LVBound k => vbvar k | LVFree x => vfvar x end.

Definition bst_nat_le_qual (u v : logic_var) : type_qualifier :=
  tqual ({[u]} ∪ {[v]}) (fun s => exists n k,
    lso_store s !! u = Some (vnat n) /\
    lso_store s !! v = Some (vnat k) /\ n <= k).

Lemma bst_nat_le_qual_value u v :
  bst_nat_le_qual u v = q_nat_le (bst_lvar_value u) (bst_lvar_value v).
Proof. destruct u,v; reflexivity. Qed.

Lemma bst_nat_le_qual_open u v j x :
  qual_open_atom j x (bst_nat_le_qual u v) =
  bst_nat_le_qual (swap (LVBound j) (LVFree x) u) (swap (LVBound j) (LVFree x) v).
Proof.
  apply qual_ext.
  - cbn [qual_open_atom bst_nat_le_qual qual_lvars].
    rewrite set_swap_union,!set_swap_singleton. reflexivity.
  - intros s1 s2 Hs.
    cbn [qual_open_atom bst_nat_le_qual qual_prop].
    unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !lstore_swap_lookup_inv_value. setoid_rewrite Hs. reflexivity.
Qed.

Lemma bst_qual_open_and j x (q1 q2 : type_qualifier) :
  qual_open_atom j x (qual_and q1 q2) =
    qual_and (qual_open_atom j x q1) (qual_open_atom j x q2).
Proof.
  destruct q1 as [D1 P1],q2 as [D2 P2]. apply qual_ext.
  - cbn [qual_open_atom qual_and qual_lvars]. apply set_swap_union.
  - intros s1 s2 Hs. cbn [qual_open_atom qual_and qual_prop].
    assert (Hcomm : forall D (HD : D ⊆ D1 ∪ D2)
      (HD' : lvars_open j x D ⊆ lvars_open j x D1 ∪ lvars_open j x D2),
      lstore_on_restrict D (lstore_on_open_back j x (D1 ∪ D2) s1) HD =
      lstore_on_open_back j x D (lstore_on_restrict (lvars_open j x D) s2 HD')).
    { intros D HD HD'. apply lstore_on_ext.
      destruct s1 as [s1 Hs1],s2 as [s2 Hs2].
      unfold lstore_on_restrict,lstore_on_open_back,storeA_on_restrict.
      cbn [lso_store storeAO_store] in Hs |- *. rewrite Hs.
      change (storeA_restrict (storeA_swap (LVBound j) (LVFree x) s2) D =
        storeA_swap (LVBound j) (LVFree x)
          (storeA_restrict s2 (set_swap (LVBound j) (LVFree x) D))).
      replace D with (set_swap (LVBound j) (LVFree x)
        (set_swap (LVBound j) (LVFree x) D)) at 1 by apply set_swap_involutive.
      apply storeA_restrict_swap. }
    match goal with |- (P1 ?s ∧ _) <-> (P1 ?t ∧ _) =>
      assert (H1 : s = t) by (eapply Hcomm)
    end.
    match goal with |- (_ ∧ P2 ?s) <-> (_ ∧ P2 ?t) =>
      assert (H2 : s = t) by (eapply Hcomm)
    end.
    rewrite H1,H2. reflexivity.
Qed.

Definition bst_range_partial_ty one : context_ty :=
  CTArrow (over_ty TNat (q_nat_le (vfvar one) ν))
    (precise_ty TNat (qual_and (q_nat_le (vfvar one) ν) (q_nat_le ν arg0))).

Definition bst_range_interval_qual one upper : type_qualifier :=
  qual_and (q_nat_le (vfvar one) ν) (q_nat_le ν (vfvar upper)).

Lemma bst_range_first_open one :
  cty_open 0 one
    (CTArrow (over_ty TNat (q_nat_le arg0 ν))
      (precise_ty TNat (qual_and (q_nat_le arg1 ν) (q_nat_le ν arg0)))) =
  bst_range_partial_ty one.
Proof.
  change (cty_open 0 one
    (CTArrow (over_ty TNat (bst_nat_le_qual (LVBound 1) (LVBound 0)))
      (precise_ty TNat (qual_and (bst_nat_le_qual (LVBound 2) (LVBound 0))
        (bst_nat_le_qual (LVBound 0) (LVBound 1))))) = bst_range_partial_ty one).
  cbn [cty_open precise_ty over_ty under_ty].
  rewrite !bst_qual_open_and,!bst_nat_le_qual_open.
  rewrite !swap_l. rewrite !swap_fresh by congruence.
  rewrite !bst_nat_le_qual_value. reflexivity.
Qed.

Lemma bst_range_second_open one upper :
  one <> upper ->
  cty_open 0 upper
    (precise_ty TNat (qual_and (q_nat_le (vfvar one) ν) (q_nat_le ν arg0))) =
  precise_ty TNat (bst_range_interval_qual one upper).
Proof.
  intros Hne.
  change (cty_open 0 upper
    (precise_ty TNat (qual_and (bst_nat_le_qual (LVFree one) (LVBound 0))
      (bst_nat_le_qual (LVBound 0) (LVBound 1)))) =
    precise_ty TNat (bst_range_interval_qual one upper)).
  cbn [cty_open precise_ty over_ty under_ty].
  rewrite !bst_qual_open_and,!bst_nat_le_qual_open.
  rewrite !swap_l. rewrite !swap_fresh by congruence.
  rewrite !bst_nat_le_qual_value. reflexivity.
Qed.

Definition bst_nat_lower_result one (s : StoreT) w : Prop :=
  exists l p, s !! one = Some (vnat l) /\ w = vnat p /\ l <= p.

Lemma bst_nat_lower_param one :
  q_nat_le (vfvar one) ν =
    param_result_qual TNat {[one]} (bst_nat_lower_result one).
Proof.
  apply qual_ext.
  - cbn [q_nat_le param_result_qual qual_lvars lvar_value_keys vnu].
    assert (H : lvars_of_atoms {[one]} = {[LVFree one]}).
    { apply set_eq. intros z. unfold lvars_of_atoms. rewrite elem_of_map. set_solver. }
    rewrite H. reflexivity.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [q_nat_le param_result_qual qual_prop lvar_value_keys denote_lvar_value
      vnu lso_store storeAO_store]. rewrite Hs.
    unfold bst_nat_lower_result,lstore_free_part. rewrite lstore_to_store_lookup.
    split.
    + intros [l [p [Hl [Hp Hlp]]]]. exists (vnat p).
      split; [exact Hp|]. split; [apply BVT_Const|]. exists l,p. auto.
    + intros [w [Hw [_ [l [p [Hl [-> Hlp]]]]]]]. exists l,p. auto.
Qed.

Definition bst_interval_result one upper (s : StoreT) w : Prop :=
  exists l h p, s !! one = Some (vnat l) /\ s !! upper = Some (vnat h) /\
    w = vnat p /\ l <= p <= h.

Lemma bst_interval_param one upper :
  bst_range_interval_qual one upper =
    param_result_qual TNat {[one;upper]} (bst_interval_result one upper).
Proof.
  apply qual_ext.
  - cbn [bst_range_interval_qual qual_and q_nat_le param_result_qual qual_lvars
      lvar_value_keys vnu].
    assert (H : lvars_of_atoms {[one;upper]} = {[LVFree one;LVFree upper]}).
    { apply set_eq. intros z. unfold lvars_of_atoms. rewrite elem_of_map. set_solver. }
    rewrite H. set_solver.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [bst_range_interval_qual qual_and q_nat_le param_result_qual qual_prop
      lvar_value_keys denote_lvar_value vnu lso_store storeAO_store].
    unfold lstore_on_restrict,storeA_on_restrict.
    cbn [lso_store storeAO_store].
    setoid_rewrite storeA_restrict_lookup.
    rewrite !decide_True by (clear; set_solver).
    rewrite Hs. unfold bst_interval_result,lstore_free_part.
    rewrite !lstore_to_store_lookup.
    split.
    + intros [[l [p [Hl [Hp Hlp]]]] [p' [h [Hp' [Hh Hph]]]]].
      assert (Hpp : p'=p) by congruence. subst p'.
      exists (vnat p). split; [exact Hp|]. split; [apply BVT_Const|].
      exists l,h,p. auto.
    + intros [w [Hw [_ [l [h [p [Hl [Hh [-> [Hlp Hph]]]]]]]]]].
      split; [exists l,p|exists p,h]; auto.
Qed.

Lemma bst_nat_singleton_param n :
  mk_q_eq (vbvar 0) (vnat n) =
    param_result_qual TNat ∅ (fun _ w => w = vnat n).
Proof.
  apply qual_ext.
  - cbn [mk_q_eq param_result_qual qual_lvars lvar_value_keys].
    unfold lvars_of_atoms. rewrite set_map_empty. set_solver.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [mk_q_eq param_result_qual qual_prop lvar_value_keys denote_lvar_value
      lso_store storeAO_store]. rewrite Hs. split.
    + intros H. exists (vnat n). split; [exact H|]. split; [apply BVT_Const|reflexivity].
    + intros [w [Hw [_ ->]]]. exact Hw.
Qed.

Definition bst_range_one_ctx n a u v g one : ctx :=
  CtxComma (bst_call_ctx n a u v g) (CtxBind one (nat_singleton_ty 1)).

Lemma bst_range_one_ctx_wf n a u v g one :
  u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  wf_ctx_under ∅ (bst_range_one_ctx n a u v g one).
Proof.
  intros Huv Hug Hvg Hone. apply wf_ctx_comma_closed_bind.
  - apply bst_call_ctx_wf; assumption.
  - cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear -Hone. set_solver.
  - apply nat_singleton_wf.
Qed.

Lemma bst_range_one_ctx_lookup n a u v g one (m : WfWorldT) σ :
  m ⊨ ctx_denote_under ∅ (bst_range_one_ctx n a u v g one) -> (m : WorldT) σ ->
  σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\ σ !! one = Some (vnat 1).
Proof.
  intros Hctx Hσ.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hbase.
  destruct (bst_call_ctx_lookup n a u v g m σ Hbase Hσ) as [Hu Hv].
  pose proof (ctx_denote_comma_closed_right ∅ _ one (nat_singleton_ty 1) m
    (nat_singleton_fv 1) Hctx) as Hone.
  split; [exact Hu|]. split; [exact Hv|]. eapply const_precise_bind_lookup; eassumption.
Qed.

Lemma bst_range_partial_wf d D one :
  one ∈ D -> wf_context_ty_at d D (bst_range_partial_ty one).
Proof.
  intros Hone.
  cbn [bst_range_partial_ty wf_context_ty_at precise_ty over_ty under_ty q_nat_le
    qual_and qual_vars qual_lvars lvar_value_keys vnu arg0 erase_ty].
  unfold lvars_wf_at. repeat split; try reflexivity.
  all: intros [j|z] Hz; cbn [lvar_wf_at] in *; clear -Hone Hz; set_solver by lia.
Qed.

Lemma bst_range_interval_wf d D one upper :
  one ∈ D -> upper ∈ D ->
  wf_context_ty_at d D (precise_ty TNat (bst_range_interval_qual one upper)).
Proof.
  intros Hone Hu. rewrite bst_interval_param.
  split; [|split; [|reflexivity]]; apply param_result_qual_wf;
    clear -Hone Hu; set_solver.
Qed.

Lemma bst_range_function_in_one_context Φ n a u v g one :
  u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  has_context_type Φ ∅ (bst_range_one_ctx n a u v g one)
    (tret (vfvar g)) bst_range_function_ty.
Proof.
  intros Huv Hug Hvg Hone.
  apply typing_comma_prefix_wf.
  - apply bst_range_one_ctx_wf; assumption.
  - apply bst_range_context_elim. split.
    + apply bst_call_ctx_wf; assumption.
    + split.
      * eapply wf_context_ty_at_mono_env; [|exact bst_range_ty_closed_wf]. set_solver.
      * apply TT_Ret, VT_FVar.
        exact (proj2 (proj2 (bst_call_ctx_lookups n a u v g Huv Hug Hvg))).
Qed.

Lemma bst_range_first_application_typed Φ n a u v g one :
  u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  has_context_type Φ ∅ (bst_range_one_ctx n a u v g one)
    (tapp (vfvar g) (vfvar one)) (bst_range_partial_ty one).
Proof.
  intros Huv Hug Hvg Hone.
  pose proof (bst_range_one_ctx_wf n a u v g one Huv Hug Hvg Hone) as HΓ.
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g)
    one (nat_singleton_ty 1) HΓ) as Ho.
  pose proof (proj2 (proj2 (bst_call_ctx_lookups n a u v g Huv Hug Hvg))) as Hg.
  rewrite <- bst_range_first_open.
  eapply CT_AppFun with (τx:=over_ty TNat qual_top).
  - split; [exact HΓ|]. split.
    + rewrite bst_range_first_open. apply bst_range_partial_wf.
      apply elem_of_dom. exists (TBase TNat). exact Ho.
    + eapply TT_App; apply VT_FVar.
      * apply erase_ctx_comma_lookup_old. exact Hg.
      * exact Ho.
  - assert (Hclosed : wf_context_ty_at 0 ∅ bst_range_function_ty)
      by exact bst_range_ty_closed_wf.
    pose proof (wf_context_ty_at_fv_subset 0 ∅ (over_ty TNat qual_top)
      (proj1 Hclosed)) as HargFV.
    pose proof (wf_context_ty_at_fv_subset 1 ∅
      (CTArrow (over_ty TNat (q_nat_le arg0 ν))
        (precise_ty TNat (qual_and (q_nat_le arg1 ν) (q_nat_le ν arg0))))
      (proj2 Hclosed)) as HbodyFV.
    cbn [fv_value]. clear -Hone HargFV HbodyFV. set_solver.
  - apply bst_range_function_in_one_context; assumption.
  - apply typing_over_top_var; assumption.
Qed.

Lemma bst_range_upper_singleton_typed Φ n a u v g one :
  u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  has_context_type Φ ∅ (bst_range_one_ctx n a u v g one)
    (tret (vfvar u)) (nat_singleton_ty n).
Proof.
  intros Huv Hug Hvg Hone.
  pose proof (bst_range_one_ctx_wf n a u v g one Huv Hug Hvg Hone) as Hw3.
  pose proof (proj1 Hw3) as Hw2. pose proof (proj1 Hw2) as Hw1.
  pose proof (proj1 Hw1) as Hw0.
  do 3 (apply typing_comma_prefix_wf; [assumption|]).
  apply typing_var_right_wf. exact Hw0.
Qed.

Lemma bst_range_upper_argument_typed Φ n a u v g one :
  0 < n -> u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  has_context_type Φ ∅ (bst_range_one_ctx n a u v g one)
    (tret (vfvar u)) (over_ty TNat (q_nat_le (vfvar one) ν)).
Proof.
  intros Hn Huv Hug Hvg Hone.
  pose proof (bst_range_one_ctx_wf n a u v g one Huv Hug Hvg Hone) as HΓ.
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g)
    one (nat_singleton_ty 1) HΓ) as Ho.
  pose proof (proj1 (bst_call_ctx_lookups n a u v g Huv Hug Hvg)) as Hu.
  assert (Htarget : wf_context_ty_at 0 (dom (erase_ctx (bst_range_one_ctx n a u v g one)))
    (over_ty TNat (q_nat_le (vfvar one) ν))).
  { rewrite bst_nat_lower_param. apply param_result_qual_wf.
    assert (HD : one ∈ dom (erase_ctx (bst_range_one_ctx n a u v g one)))
      by (apply elem_of_dom; eauto).
    clear -HD. set_solver. }
  eapply CT_Sub.
  - split; [exact HΓ|]. split; [exact Htarget|].
    apply TT_Ret, VT_FVar. apply erase_ctx_comma_lookup_old. exact Hu.
  - exact (typing_inter_l _ _ _ _ _ _
      (bst_range_upper_singleton_typed Φ n a u v g one Huv Hug Hvg Hone)).
  - apply sub_type_over_store_consequence; [exact HΓ| |exact Htarget|].
    + exact (proj1 (nat_singleton_wf 0 _ n)).
    + intros m y σ w Hctx Hσ Hy Hq.
      change (qualifier_holds_store (qual_open_atom 0 y
        (typed_result_qual TNat (mk_q_eq (vbvar 0) (vnat n)))) (<[y:=w]> σ)) in Hq.
      rewrite bst_nat_singleton_param in Hq.
      apply typed_param_result_qual_open_store in Hq; [|set_solver].
      destruct Hq as [_ [w' [Hyw [_ ->]]]].
      assert (Hw : w = vnat n).
      { assert (Hsame : Some w = Some (vnat n)).
        { transitivity ((<[y:=w]> σ : StoreT) !! y);
            [symmetry; apply map_lookup_insert|exact Hyw]. }
        now inversion Hsame. }
      subst w.
      destruct (bst_range_one_ctx_lookup n a u v g one m σ Hctx Hσ) as [_ [_ H1]].
      assert (Hy1 : y <> one).
      { rewrite bst_nat_lower_param,param_result_qual_dom in Hy.
        clear -Hy. set_solver. }
      rewrite bst_nat_lower_param. apply typed_param_result_qual_open_store;
        [clear -Hy1; set_solver|].
      split.
      * rewrite store_insert_dom. assert (HD : one ∈ (dom (σ : gmap atom value) : aset))
          by (apply elem_of_dom; eauto). clear -HD. set_solver.
      * exists (vnat n). split; [apply map_lookup_insert|]. split; [apply BVT_Const|].
        exists 1,n. split.
        -- rewrite store_restrict_lookup_at by (clear; set_solver).
           rewrite store_insert_lookup_ne by congruence. exact H1.
        -- split; [reflexivity|lia].
Qed.

Lemma bst_range_interval_pivot_open n u v one y (σ : StoreT) :
  y ∉ ({[u;v;one]} : aset) -> ({[u;v;one]} : aset) ⊆ dom (σ : StoreT) ->
  σ !! one = Some (vnat 1) -> σ !! u = Some (vnat n) ->
  (qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TNat
    (bst_range_interval_qual one u))) σ <->
   qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TNat
    (bst_pivot_qual {[u;v]} n))) σ).
Proof.
  intros Hy Hscope H1 Hu.
  rewrite bst_interval_param. unfold bst_pivot_qual.
  rewrite !typed_param_result_qual_open_store by (clear -Hy; set_solver).
  unfold bst_interval_result. split.
  - intros [_ [w [Hyw [_ [l [h [p [Hl [Hh [-> Hp]]]]]]]]]].
    rewrite !store_restrict_lookup_at in Hl,Hh by (clear; set_solver).
    assert (Hl1 : l=1) by (eapply store_nat_lookup_unique; eassumption).
    assert (Hhn : h=n) by (eapply store_nat_lookup_unique; eassumption).
    subst l h. split; [clear -Hscope; set_solver|].
    exists (vnat p). split; [exact Hyw|]. split; [apply BVT_Const|]. exists p. auto.
  - intros [_ [w [Hyw [_ [p [-> Hp]]]]]].
    split; [clear -Hscope; set_solver|]. exists (vnat p).
    split; [exact Hyw|]. split; [apply BVT_Const|]. exists 1,n,p.
    split; [rewrite store_restrict_lookup_at by (clear; set_solver); exact H1|].
    split; [rewrite store_restrict_lookup_at by (clear; set_solver); exact Hu|]. auto.
Qed.

Lemma bst_range_raw_pivot_subtype n a u v g one :
  u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  sub_type_under ∅ (bst_range_one_ctx n a u v g one)
    (precise_ty TNat (bst_range_interval_qual one u))
    (precise_ty TNat (bst_pivot_qual {[u;v]} n)).
Proof.
  intros Huv Hug Hvg Hone.
  set (Γ := bst_range_one_ctx n a u v g one).
  pose proof (bst_range_one_ctx_wf n a u v g one Huv Hug Hvg Hone) as HΓ.
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g)
    one (nat_singleton_ty 1) HΓ) as Ho.
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  assert (HuD : u ∈ dom (erase_ctx Γ)).
  { apply elem_of_dom. exists (TBase TNat). apply erase_ctx_comma_lookup_old. exact Hu. }
  assert (HvD : v ∈ dom (erase_ctx Γ)).
  { apply elem_of_dom. exists (TBase TNat). apply erase_ctx_comma_lookup_old. exact Hv. }
  assert (HoD : one ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (HF : ({[u;v;one]} : aset) ⊆ dom (erase_ctx Γ))
    by (clear -HuD HvD HoD; set_solver).
  assert (Hraw : wf_context_ty_at 0 (dom (erase_ctx Γ))
    (precise_ty TNat (bst_range_interval_qual one u)))
    by (apply bst_range_interval_wf; assumption).
  assert (Htarget : wf_context_ty_at 0 (dom (erase_ctx Γ))
    (precise_ty TNat (bst_pivot_qual {[u;v]} n))).
  { split; [|split; [|reflexivity]]; unfold bst_pivot_qual;
      apply param_result_qual_wf; clear -HuD HvD; set_solver. }
  apply sub_type_under_inter_intro; [| |exact Htarget].
  - eapply sub_type_under_trans; [apply sub_type_under_inter_l; eassumption|].
    apply sub_type_over_store_consequence;
      [exact HΓ|exact (proj1 Hraw)|exact (proj1 Htarget)|].
    intros m y σ w Hctx Hσ Hy Hq.
    assert (HyF : y ∉ ({[u;v;one]} : aset)).
    { rewrite bst_interval_param in Hy. unfold bst_pivot_qual in Hy.
      rewrite !param_result_qual_dom in Hy. clear -Hy. set_solver. }
    destruct (bst_range_one_ctx_lookup n a u v g one m σ Hctx Hσ) as [Hn [_ H1]].
    assert (HQ : ({[u;v;one]} : aset) ⊆ dom (<[y:=w]> σ : StoreT)).
    { rewrite store_insert_dom.
      pose proof (ctx_denote_under_store_scope ∅ Γ m σ Hctx Hσ) as HD.
      clear -HD HF. set_solver. }
    assert (H1Q : (<[y:=w]> σ : StoreT) !! one = Some (vnat 1)).
    { rewrite store_insert_lookup_ne by (clear -HyF; set_solver). exact H1. }
    assert (HnQ : (<[y:=w]> σ : StoreT) !! u = Some (vnat n)).
    { rewrite store_insert_lookup_ne by (clear -HyF; set_solver). exact Hn. }
    exact (proj1 (bst_range_interval_pivot_open n u v one y (<[y:=w]> σ)
      HyF HQ H1Q HnQ) Hq).
  - eapply sub_type_under_trans; [apply sub_type_under_inter_r; eassumption|].
    eapply sub_type_under_worldwise_fixed with (F:={[u;v;one]});
      [exact HΓ|exact (proj1 (proj2 Hraw))|exact (proj1 (proj2 Htarget))| | |].
    + rewrite bst_interval_param,param_result_qual_dom.
      change (({[one;u]} : gset atom) ⊆ {[u;v;one]}). clear; set_solver.
    + unfold bst_pivot_qual. rewrite param_result_qual_dom.
      change (({[u;v]} : gset atom) ⊆ {[u;v;one]}). clear; set_solver.
    + intros m Hctx. destruct (world_wf m) as [[σ Hσ] _].
      destruct (bst_range_one_ctx_lookup n a u v g one m σ Hctx Hσ) as [Hn [Ha H1]].
      exists (store_restrict σ {[u;v;one]}). split.
      * intros τ Hτ.
        destruct (bst_range_one_ctx_lookup n a u v g one m τ Hctx Hτ) as [Hn' [Ha' H1']].
        apply store_restrict_eq_on. intros z Hz.
        assert (Hz' : z=u \/ z=v \/ z=one) by (clear -Hz; set_solver).
        destruct Hz' as [Heqz|[Heqz|Heqz]]; subst z;
          first [exact (eq_trans Hn' (eq_sym Hn))|
            exact (eq_trans Ha' (eq_sym Ha))|exact (eq_trans H1' (eq_sym H1))].
      * intros y τ Hy Hτ. apply bst_range_interval_pivot_open; [exact Hy| | |].
        -- eapply store_restrict_eq_scope; [|exact (eq_sym Hτ)].
           etransitivity; [exact HF|exact (ctx_denote_under_store_scope ∅ Γ m σ Hctx Hσ)].
        -- eapply (store_restrict_eq_lookup σ τ {[u;v;one]} one);
             [clear; set_solver|exact (eq_sym Hτ)|exact H1].
        -- eapply (store_restrict_eq_lookup σ τ {[u;v;one]} u);
             [clear; set_solver|exact (eq_sym Hτ)|exact Hn].
Qed.

Lemma bst_range_function_context_wf n a u v g one fn :
  u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  fn ∉ ({[u;v;g;one]} : aset) ->
  wf_ctx_under ∅ (CtxComma (bst_range_one_ctx n a u v g one)
    (CtxBind fn (bst_range_partial_ty one))).
Proof.
  intros Huv Hug Hvg Hone Hfn. apply bst_positive_bind_wf.
  - apply bst_range_one_ctx_wf; assumption.
  - cbn [ctx_dom bst_range_one_ctx bst_call_ctx nat_pair_ctx]. clear -Hfn. set_solver.
  - apply bst_range_partial_wf.
    cbn [ctx_dom bst_range_one_ctx bst_call_ctx nat_pair_ctx]. clear; set_solver.
Qed.

Lemma bst_range_second_application_typed Φ n a u v g one fn :
  0 < n -> u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  fn ∉ ({[u;v;g;one]} : aset) ->
  has_context_type Φ ∅ (CtxComma (bst_range_one_ctx n a u v g one)
    (CtxBind fn (bst_range_partial_ty one)))
    (tapp (vfvar fn) (vfvar u)) (precise_ty TNat (bst_range_interval_qual one u)).
Proof.
  intros Hn Huv Hug Hvg Hone Hfn.
  pose proof (bst_range_function_context_wf n a u v g one fn Huv Hug Hvg Hone Hfn) as HΓ.
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_range_one_ctx n a u v g one)
    fn (bst_range_partial_ty one) HΓ) as Hf.
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g)
    one (nat_singleton_ty 1) (proj1 HΓ)) as Ho.
  pose proof (proj1 (bst_call_ctx_lookups n a u v g Huv Hug Hvg)) as Hu.
  assert (Honeu : one <> u) by (clear -Hone; set_solver).
  rewrite <- bst_range_second_open by exact Honeu.
  eapply CT_AppFun with (τx:=over_ty TNat (q_nat_le (vfvar one) ν)).
  - split; [exact HΓ|]. split.
    + rewrite bst_range_second_open by exact Honeu. apply bst_range_interval_wf.
      * apply elem_of_dom. exists (TBase TNat). apply erase_ctx_comma_lookup_old. exact Ho.
      * apply elem_of_dom. exists (TBase TNat). do 2 apply erase_ctx_comma_lookup_old. exact Hu.
    + eapply TT_App; apply VT_FVar.
      * exact Hf.
      * do 2 apply erase_ctx_comma_lookup_old. exact Hu.
  - assert (Hpartial : wf_context_ty_at 0 {[one]} (bst_range_partial_ty one))
      by (apply bst_range_partial_wf; set_solver).
    pose proof (wf_context_ty_at_fv_subset 0 {[one]}
      (over_ty TNat (q_nat_le (vfvar one) ν)) (proj1 Hpartial)) as HargFV.
    pose proof (wf_context_ty_at_fv_subset 1 {[one]}
      (precise_ty TNat (qual_and (q_nat_le (vfvar one) ν) (q_nat_le ν arg0)))
      (proj2 Hpartial)) as HresultFV.
    cbn [fv_value]. clear -HargFV HresultFV Honeu Hfn. set_solver.
  - apply typing_var_right_wf. exact HΓ.
  - apply typing_comma_prefix_wf; [exact HΓ|].
    apply bst_range_upper_argument_typed; assumption.
Qed.

Lemma bst_range_app2_raw_typed Φ n a u v g one :
  0 < n -> u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  has_context_type Φ ∅ (bst_range_one_ctx n a u v g one)
    (NatArithmetic.app2 (vfvar g) (vfvar one) (vfvar u))
    (precise_ty TNat (bst_range_interval_qual one u)).
Proof.
  intros Hn Huv Hug Hvg Hone.
  pose proof (bst_range_first_application_typed Φ n a u v g one Huv Hug Hvg Hone) as Hfirst.
  pose proof (typing_wf_under _ _ _ _ _ Hfirst) as [HΓ [Hpartial Hbasic]].
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g)
    one (nat_singleton_ty 1) HΓ) as Ho.
  pose proof (proj1 (bst_call_ctx_lookups n a u v g Huv Hug Hvg)) as Hu.
  unfold NatArithmetic.app2,tapp_tm. cbn [value_shift].
  eapply CT_Let with (τ1:=bst_range_partial_ty one) (L:={[u;v;g;one]}).
  - split; [exact HΓ|]. split.
    + apply bst_range_interval_wf; apply elem_of_dom; exists (TBase TNat).
      * exact Ho.
      * apply erase_ctx_comma_lookup_old. exact Hu.
    + change (tm_has_type (erase_ctx (bst_range_one_ctx n a u v g one))
        (tapp_tm (tapp (vfvar g) (vfvar one)) (vfvar u)) (TBase TNat)).
      eapply basic_typing_tapp_tm; [exact Hbasic|].
      apply VT_FVar. apply erase_ctx_comma_lookup_old. exact Hu.
  - exact Hfirst.
  - intros fn Hfn.
    change (has_context_type Φ ∅ (CtxComma (bst_range_one_ctx n a u v g one)
      (CtxBind fn (bst_range_partial_ty one))) (tapp (vfvar fn) (vfvar u))
      (precise_ty TNat (bst_range_interval_qual one u))).
    apply bst_range_second_application_typed; assumption.
Qed.

Lemma bst_range_app2_var_typed Φ n a u v g one :
  0 < n -> u <> v -> u <> g -> v <> g -> one ∉ ({[u;v;g]} : aset) ->
  has_context_type Φ ∅ (bst_range_one_ctx n a u v g one)
    (NatArithmetic.app2 (vfvar g) (vfvar one) (vfvar u))
    (precise_ty TNat (bst_pivot_qual {[u;v]} n)).
Proof.
  intros Hn Huv Hug Hvg Hone.
  pose proof (bst_range_app2_raw_typed Φ n a u v g one Hn Huv Hug Hvg Hone) as Hraw.
  pose proof (bst_range_raw_pivot_subtype n a u v g one Huv Hug Hvg Hone) as Hsub.
  eapply CT_Sub; [|exact Hraw|exact Hsub].
  pose proof (typing_wf_under _ _ _ _ _ Hraw) as [HΓ [_ He]].
  split; [exact HΓ|]. split; [exact (proj1 (proj2 (proj2 Hsub)))|exact He].
Qed.

Definition bst_range_proxy f upper : tm :=
  tlete (tret (vnat 1)) (NatArithmetic.app2 f (vbvar 0) upper).

Lemma bst_range_proxy_open f upper w :
  lc_value f -> lc_value upper ->
  open_tm 0 w (NatArithmetic.app2 f (vbvar 0) upper) = NatArithmetic.app2 f w upper.
Proof.
  intros Hf Hu. unfold NatArithmetic.app2.
  rewrite open_tapp_tm_lc_arg by exact Hu. cbn [open_tm open_value].
  rewrite (open_rec_lc_value f Hf 0 w). reflexivity.
Qed.

Lemma bst_range_proxy_prefix f upper :
  lc_value f -> lc_value upper ->
  arithmetic_prefix (bst_range_proxy f upper) (NatArithmetic.app2 f (vnat 1) upper).
Proof.
  intros Hf Hu.
  assert (Hlc : lc_tm (bst_range_proxy f upper)).
  { unfold bst_range_proxy. eapply LC_lete with (L:=∅).
    - repeat constructor.
    - intros x _. rewrite bst_range_proxy_open by assumption.
      unfold NatArithmetic.app2. apply lc_tapp_tm; [apply LC_app; [exact Hf|constructor]|exact Hu]. }
  assert (Hhead : head_step (bst_range_proxy f upper)
    (NatArithmetic.app2 f (vnat 1) upper)).
  { rewrite <- (bst_range_proxy_open f upper (vnat 1) Hf Hu).
    apply HS_Ret. exact Hlc. }
  eapply Prefix_step; [|apply Prefix_refl]. split.
  - apply Step_head. exact Hhead.
  - eapply arithmetic_head_deterministic; [exact Hhead|].
    intros op c Hbad. discriminate.
Qed.

Lemma bst_range_proxy_basic Δ g u :
  Δ !! g = Some (TNat →ᵦ TNat →ᵦ TNat) -> Δ !! u = Some (TBase TNat) ->
  tm_has_type Δ (bst_range_proxy (vfvar g) (vfvar u)) (TBase TNat).
Proof.
  intros Hg Hu. unfold bst_range_proxy.
  eapply TT_Let with (L:=({[g;u]} : aset)).
  - apply TT_Ret,VT_Const.
  - intros one Hone.
    change (tm_has_type (<[one:=TBase TNat]> Δ)
      (NatArithmetic.app2 (vfvar g) (vfvar one) (vfvar u)) (TBase TNat)).
    unfold NatArithmetic.app2. eapply basic_typing_tapp_tm.
    + eapply TT_App; apply VT_FVar.
      * exact (eq_trans (map_lookup_insert_ne Δ one g (TBase TNat)
          ltac:(clear -Hone; set_solver)) Hg).
      * apply map_lookup_insert.
    + apply VT_FVar. exact (eq_trans (map_lookup_insert_ne Δ one u (TBase TNat)
        ltac:(clear -Hone; set_solver)) Hu).
Qed.

Lemma bst_range_proxy_context_typed Φ n a u v g :
  0 < n -> u <> v -> u <> g -> v <> g ->
  has_context_type Φ ∅ (bst_call_ctx n a u v g)
    (bst_range_proxy (vfvar g) (vfvar u)) (precise_ty TNat (bst_pivot_qual {[u;v]} n)).
Proof.
  intros Hn Huv Hug Hvg.
  pose proof (bst_call_ctx_wf n a u v g Huv Hug Hvg) as HΓ.
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  unfold bst_range_proxy. eapply CT_Let with (τ1:=nat_singleton_ty 1) (L:={[u;v;g]}).
  - split; [exact HΓ|]. split.
    + split; [|split; [|reflexivity]]; unfold bst_pivot_qual; apply param_result_qual_wf;
        assert (HuD : u ∈ dom (erase_ctx (bst_call_ctx n a u v g)))
          by (apply elem_of_dom; eauto);
        assert (HvD : v ∈ dom (erase_ctx (bst_call_ctx n a u v g)))
          by (apply elem_of_dom; eauto);
        clear -HuD HvD; set_solver.
    + exact (bst_range_proxy_basic _ g u Hg Hu).
  - apply typing_const_in_ctx. split; [exact HΓ|].
    split; [apply const_precise_wf|apply TT_Ret,VT_Const].
  - intros one Hone.
    change (has_context_type Φ ∅ (bst_range_one_ctx n a u v g one)
      (NatArithmetic.app2 (vfvar g) (vfvar one) (vfvar u))
      (precise_ty TNat (bst_pivot_qual {[u;v]} n))).
    apply bst_range_app2_var_typed; assumption.
Qed.

Lemma bst_range_proxy_instantiate σ g u f n :
  σ !! g = Some f -> σ !! u = Some (vnat n) ->
  lstore_instantiate_tm (lstore_lift_free σ) (bst_range_proxy (vfvar g) (vfvar u)) =
    bst_range_proxy f (vnat n).
Proof.
  intros Hg Hu. arithmetic_instantiate. setoid_rewrite Hg. setoid_rewrite Hu.
  reflexivity.
Qed.

Lemma bst_range_call_instantiate σ g u f n :
  σ !! g = Some f -> σ !! u = Some (vnat n) ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (NatArithmetic.app2 (vfvar g) (vnat 1) (vfvar u)) =
    NatArithmetic.app2 f (vnat 1) (vnat n).
Proof.
  intros Hg Hu. arithmetic_instantiate. setoid_rewrite Hg. setoid_rewrite Hu.
  reflexivity.
Qed.

Lemma bst_range_call_context_typed Φ n a u v g :
  0 < n -> u <> v -> u <> g -> v <> g ->
  has_context_type Φ ∅ (bst_call_ctx n a u v g)
    (NatArithmetic.app2 (vfvar g) (vnat 1) (vfvar u))
    (precise_ty TNat (bst_pivot_qual {[u;v]} n)).
Proof.
  intros Hn Huv Hug Hvg.
  pose proof (bst_range_proxy_context_typed Φ n a u v g Hn Huv Hug Hvg) as Hproxy.
  pose proof (typing_wf_under _ _ _ _ _ Hproxy) as [HΓ [Htarget _]].
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  eapply CT_Conv; [|exact Hproxy|].
  - split; [exact HΓ|]. split; [exact Htarget|].
    unfold NatArithmetic.app2. eapply basic_typing_tapp_tm.
    + eapply TT_App; [apply VT_FVar; exact Hg|apply VT_Const].
    + apply VT_FVar. exact Hu.
  - intros m Hctx.
    assert (Hargs : forall σ, (m : WorldT) σ -> exists f,
      σ !! g = Some f /\ σ !! u = Some (vnat n) /\ lc_value f).
    { intros σ Hσ.
      destruct (ctx_denote_under_lookup_typed ∅ _ g _ m σ HΓ Hg Hctx Hσ)
        as [f [Hgf Hft]].
      pose proof (proj1 (bst_call_ctx_lookup n a u v g m σ Hctx Hσ)) as Hnu.
      exists f. split; [exact Hgf|]. split; [exact Hnu|].
      exact (typing_value_lc _ _ _ Hft). }
    split.
    + intros σ w Hσ. destruct (Hargs σ Hσ) as [f [Hgf [Hnu Hflc]]].
      unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (bst_range_proxy_instantiate _ _ _ _ _ Hgf Hnu),
        (bst_range_call_instantiate _ _ _ _ _ Hgf Hnu).
      exact (proj1 (arithmetic_prefix_equivalence _ _
        (bst_range_proxy_prefix f (vnat n) Hflc (LC_const _))) w).
    + intros σ Hσ. destruct (Hargs σ Hσ) as [f [Hgf [Hnu Hflc]]].
      rewrite (bst_range_proxy_instantiate _ _ _ _ _ Hgf Hnu),
        (bst_range_call_instantiate _ _ _ _ _ Hgf Hnu).
      exact (proj2 (arithmetic_prefix_equivalence _ _
        (bst_range_proxy_prefix f (vnat n) Hflc (LC_const _)))).
Qed.
