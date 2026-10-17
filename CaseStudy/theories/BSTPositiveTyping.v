(** Compose the original six lets.  The stage definitions expose the same
    nameless syntax, without changing the generator or its recursive calls. *)
From CaseStudy Require Import BSTGeneratorProgram BSTGeneratorUnfolding BSTContext
  BSTNodeTypes BSTPositiveContext BSTRangeTyping BSTArithmeticSupport
  BSTRecursiveCases BSTRightRecursiveCases BSTSupport
  NatArithmetic NatArithmeticTyping NatArithmeticApplications.
From ContextTyping Require Import Typing TypingRegular BasicBindings Subtyping
  NatCases PrimOpConcreteContext SoundnessLam.
From Denotation Require Import Context ResultQualifier TypeDenoteRegular TypeEquivCore TypeEquiv.
From CoreLang Require Import Sugar BasicTypingProps Choice.

Definition bst_right_stage vg vrs vk vl : tm :=
  tlete (NatArithmetic.app3 bst_gen_value vrs vk vg)
    (tnode (value_shift 0 vk) (value_shift 0 vl) (vbvar 0)).

Definition bst_left_stage vlo vg vls vrs vk : tm :=
  tlete (NatArithmetic.app3 bst_gen_value vls vlo vg)
    (bst_right_stage (value_shift 0 vg) (value_shift 0 vrs) (value_shift 0 vk) (vbvar 0)).

Definition bst_root_stage vlo vg vp vls vrs : tm :=
  tlete (NatArithmetic.app2 NatArithmetic.add_value vlo vp)
    (bst_left_stage (value_shift 0 vlo) (value_shift 0 vg)
      (value_shift 0 vls) (value_shift 0 vrs) (vbvar 0)).

Definition bst_sub_stage vr vlo vg vp vls : tm :=
  tlete (NatArithmetic.app2 NatArithmetic.sub_value vr vp)
    (bst_root_stage (value_shift 0 vlo) (value_shift 0 vg)
      (value_shift 0 vp) (value_shift 0 vls) (vbvar 0)).

Definition bst_pred_stage vr vlo vg vp : tm :=
  tlete (tprim op_minus1 vp)
    (bst_sub_stage (value_shift 0 vr) (value_shift 0 vlo)
      (value_shift 0 vg) (value_shift 0 vp) (vbvar 0)).

Definition bst_generate_stage vr vlo vg : tm :=
  tlete (NatArithmetic.app2 vg (vnat 1) vr)
    (bst_pred_stage (value_shift 0 vr) (value_shift 0 vlo) (value_shift 0 vg) (vbvar 0)).

Lemma bst_positive_branch_generate u v g :
  bst_positive_branch (vfvar u) (vfvar v) (vfvar g) =
  NatArithmetic.choose (tret (vconst (ctree tr_leaf)))
    (bst_generate_stage (vfvar u) (vfvar v) (vfvar g)).
Proof. vm_compute. reflexivity. Qed.

Lemma bst_stage_insert_lookup (Δ : gmap atom ty) x y U T :
  x <> y -> Δ !! y = Some T -> (<[x:=U]> Δ) !! y = Some T.
Proof.
  intros Hxy Hy. exact (eq_trans (map_lookup_insert_ne Δ x y U ltac:(congruence)) Hy).
Qed.

(** The induction premise always concerns the actual closed generator. *)
Definition bst_smaller_calls_typed (n : nat) : Prop :=
  forall m a u v g, m < n -> u <> v -> u <> g -> v <> g ->
    has_context_type concrete_Φ ∅ (bst_call_ctx m a u v g)
      (NatArithmetic.app3 bst_gen_value (vfvar u) (vfvar v) (vfvar g))
      (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).

Lemma bst_stage_result_wf Γ n a u v :
  erase_ctx Γ !! u = Some (TBase TNat) ->
  erase_ctx Γ !! v = Some (TBase TNat) ->
  wf_context_ty_at 0 (dom (erase_ctx Γ))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hu Hv. unfold bst_result_qual. apply param_result_qual_wf.
  assert (HuD : u ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  assert (HvD : v ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
  clear -HuD HvD. set_solver.
Qed.

Local Ltac bst_stage_lookup Hnew :=
  first [assumption | apply map_lookup_insert |
    eapply bst_stage_insert_lookup; [clear -Hnew; set_solver|eassumption]].

Lemma bst_right_stage_basic Δ g rs k l :
  Δ !! g = Some BSTProgram.range_basic_ty -> Δ !! rs = Some (TBase TNat) ->
  Δ !! k = Some (TBase TNat) -> Δ !! l = Some (TBase TTree) ->
  tm_has_type Δ (bst_right_stage (vfvar g) (vfvar rs) (vfvar k) (vfvar l)) (TBase TTree).
Proof.
  intros Hg Hrs Hk Hl. unfold bst_right_stage.
  eapply TT_Let with (L:=({[k;l]} : aset)).
  - apply bst_call_variables_basic_typed; assumption.
  - intros xr Hxr.
    change (tm_has_type (<[xr:=TBase TTree]> Δ)
      (tnode (vfvar k) (vfvar l) (vfvar xr)) (TBase TTree)).
    apply TT_TreeNode; apply VT_FVar; bst_stage_lookup Hxr.
Qed.

Lemma bst_left_stage_basic Δ lo g ls rs k :
  Δ !! lo = Some (TBase TNat) -> Δ !! g = Some BSTProgram.range_basic_ty ->
  Δ !! ls = Some (TBase TNat) -> Δ !! rs = Some (TBase TNat) -> Δ !! k = Some (TBase TNat) ->
  tm_has_type Δ (bst_left_stage (vfvar lo) (vfvar g) (vfvar ls) (vfvar rs) (vfvar k))
    (TBase TTree).
Proof.
  intros Hlo Hg Hls Hrs Hk. unfold bst_left_stage.
  eapply TT_Let with (L:=({[g;rs;k]} : aset)).
  - apply bst_call_variables_basic_typed; assumption.
  - intros xl Hxl.
    change (tm_has_type (<[xl:=TBase TTree]> Δ)
      (bst_right_stage (vfvar g) (vfvar rs) (vfvar k) (vfvar xl)) (TBase TTree)).
    apply bst_right_stage_basic; bst_stage_lookup Hxl.
Qed.

Lemma bst_root_stage_basic Δ lo g p ls rs :
  Δ !! lo = Some (TBase TNat) -> Δ !! g = Some BSTProgram.range_basic_ty ->
  Δ !! p = Some (TBase TNat) -> Δ !! ls = Some (TBase TNat) -> Δ !! rs = Some (TBase TNat) ->
  tm_has_type Δ (bst_root_stage (vfvar lo) (vfvar g) (vfvar p) (vfvar ls) (vfvar rs))
    (TBase TTree).
Proof.
  intros Hlo Hg Hp Hls Hrs. unfold bst_root_stage.
  eapply TT_Let with (L:=({[lo;g;ls;rs]} : aset)).
  - apply (arithmetic_app2_basic true); assumption.
  - intros k Hk.
    change (tm_has_type (<[k:=TBase TNat]> Δ)
      (bst_left_stage (vfvar lo) (vfvar g) (vfvar ls) (vfvar rs) (vfvar k)) (TBase TTree)).
    apply bst_left_stage_basic; bst_stage_lookup Hk.
Qed.

Lemma bst_sub_stage_basic Δ r lo g p ls :
  Δ !! r = Some (TBase TNat) -> Δ !! lo = Some (TBase TNat) ->
  Δ !! g = Some BSTProgram.range_basic_ty -> Δ !! p = Some (TBase TNat) ->
  Δ !! ls = Some (TBase TNat) ->
  tm_has_type Δ (bst_sub_stage (vfvar r) (vfvar lo) (vfvar g) (vfvar p) (vfvar ls))
    (TBase TTree).
Proof.
  intros Hr Hlo Hg Hp Hls. unfold bst_sub_stage.
  eapply TT_Let with (L:=({[lo;g;p;ls]} : aset)).
  - apply (arithmetic_app2_basic false); assumption.
  - intros rs Hrs.
    change (tm_has_type (<[rs:=TBase TNat]> Δ)
      (bst_root_stage (vfvar lo) (vfvar g) (vfvar p) (vfvar ls) (vfvar rs)) (TBase TTree)).
    apply bst_root_stage_basic; bst_stage_lookup Hrs.
Qed.

Lemma bst_pred_stage_basic Δ r lo g p :
  Δ !! r = Some (TBase TNat) -> Δ !! lo = Some (TBase TNat) ->
  Δ !! g = Some BSTProgram.range_basic_ty -> Δ !! p = Some (TBase TNat) ->
  tm_has_type Δ (bst_pred_stage (vfvar r) (vfvar lo) (vfvar g) (vfvar p)) (TBase TTree).
Proof.
  intros Hr Hlo Hg Hp. unfold bst_pred_stage.
  eapply TT_Let with (L:=({[r;lo;g;p]} : aset)).
  - eapply TT_Op; [reflexivity|apply VT_FVar; exact Hp].
  - intros ls Hls.
    change (tm_has_type (<[ls:=TBase TNat]> Δ)
      (bst_sub_stage (vfvar r) (vfvar lo) (vfvar g) (vfvar p) (vfvar ls)) (TBase TTree)).
    apply bst_sub_stage_basic; bst_stage_lookup Hls.
Qed.

Lemma bst_generate_stage_basic Δ r lo g :
  Δ !! r = Some (TBase TNat) -> Δ !! lo = Some (TBase TNat) ->
  Δ !! g = Some BSTProgram.range_basic_ty ->
  tm_has_type Δ (bst_generate_stage (vfvar r) (vfvar lo) (vfvar g)) (TBase TTree).
Proof.
  intros Hr Hlo Hg. unfold bst_generate_stage.
  eapply TT_Let with (L:=({[r;lo;g]} : aset)).
  - unfold NatArithmetic.app2. eapply basic_typing_tapp_tm; [|apply VT_FVar; exact Hr].
    eapply TT_App; [apply VT_FVar; exact Hg|apply VT_Const].
  - intros p Hp.
    change (tm_has_type (<[p:=TBase TNat]> Δ)
      (bst_pred_stage (vfvar r) (vfvar lo) (vfvar g) (vfvar p)) (TBase TTree)).
    apply bst_pred_stage_basic; bst_stage_lookup Hp.
Qed.

Lemma bst_right_stage_context_typed n a u v g xp ls rs k xl :
  0 < n -> u <> v -> u <> g -> v <> g ->
  xp ∉ ({[u;v;g]} : aset) -> ls ∉ ({[u;v;g;xp]} : aset) ->
  rs ∉ ({[u;v;g;xp;ls]} : aset) -> k ∉ ({[u;v;g;xp;ls;rs]} : aset) ->
  xl ∉ ({[u;v;g;xp;ls;rs;k]} : aset) -> bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_left_tree_ctx n a u v g xp ls rs k xl)
    (bst_right_stage (vfvar g) (vfvar rs) (vfvar k) (vfvar xl))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hn Huv Hug Hvg Hxp Hls Hrs Hk Hxl HIH.
  pose proof (bst_root_ctx_wf n a u v g xp ls rs k Huv Hug Hvg Hxp Hls Hrs Hk) as Hw4.
  pose proof (bst_left_tree_ctx_wf n a u v g xp ls rs k xl Hw4 Hxl) as HΓ.
  pose proof (bst_right_case_ctx_wf n a 0 tr_leaf u v g xp ls rs k xl
    Huv Hug Hvg Hxp Hls Hrs Hk Hxl) as Hcase.
  destruct (bst_right_case_erasure_lookups n a 0 tr_leaf u v g xp ls rs k xl
    Huv Hug Hvg Hcase) as [Hu [Hv [Hg [Hp [Hsl [Hsr [Hkr Hlt]]]]]]].
  unfold bst_right_stage.
  eapply CT_Let with
    (τ1:=CTUnder TTree (bst_right_qual {[u;v]} xp xl n a))
    (L:=({[u;v;g;xp;ls;rs;k;xl]} : aset)).
  - split; [exact HΓ|]. split.
    + apply bst_stage_result_wf; eassumption.
    + change (tm_has_type (erase_ctx (bst_left_tree_ctx n a u v g xp ls rs k xl))
        (bst_right_stage (vfvar g) (vfvar rs) (vfvar k) (vfvar xl)) (TBase TTree)).
      apply bst_right_stage_basic; assumption.
  - eapply bst_right_call_positive_context_typed; try eassumption.
    intros p Hp' Hdec. apply HIH; [exact Hdec| | | ]; clear -Hrs Hk; set_solver.
  - intros xr Hxr.
    change (has_context_type concrete_Φ ∅ (bst_right_tree_ctx n a u v g xp ls rs k xl xr)
      (tnode (vfvar k) (vfvar xl) (vfvar xr))
      (CTUnder TTree (bst_result_qual {[u;v]} n a))).
    apply bst_positive_node_context_typed; assumption.
Qed.

Lemma bst_left_stage_context_typed n a u v g xp ls rs k :
  0 < n -> u <> v -> u <> g -> v <> g ->
  xp ∉ ({[u;v;g]} : aset) -> ls ∉ ({[u;v;g;xp]} : aset) ->
  rs ∉ ({[u;v;g;xp;ls]} : aset) -> k ∉ ({[u;v;g;xp;ls;rs]} : aset) ->
  bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_root_ctx n a u v g xp ls rs k)
    (bst_left_stage (vfvar v) (vfvar g) (vfvar ls) (vfvar rs) (vfvar k))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hn Huv Hug Hvg Hxp Hls Hrs Hk HIH.
  pose proof (bst_root_ctx_wf n a u v g xp ls rs k Huv Hug Hvg Hxp Hls Hrs Hk) as HΓ.
  pose proof (bst_left_case_ctx_wf n a 0 u v g xp ls rs k
    Huv Hug Hvg Hxp Hls Hrs Hk) as Hcase.
  destruct (bst_left_case_erasure_lookups n a 0 u v g xp ls rs k
    Huv Hug Hvg Hcase) as [Hu [Hv [Hg [Hp [Hsl [Hsr Hkr]]]]]].
  unfold bst_left_stage.
  eapply CT_Let with (τ1:=CTUnder TTree (bst_left_qual {[u;v]} xp n a))
    (L:=({[u;v;g;xp;ls;rs;k]} : aset)).
  - split; [exact HΓ|]. split.
    + apply bst_stage_result_wf; eassumption.
    + change (tm_has_type (erase_ctx (bst_root_ctx n a u v g xp ls rs k))
        (bst_left_stage (vfvar v) (vfvar g) (vfvar ls) (vfvar rs) (vfvar k)) (TBase TTree)).
      apply bst_left_stage_basic; assumption.
  - eapply bst_left_call_positive_context_typed; try eassumption.
    intros p Hp' Hdec. apply HIH; [exact Hdec| | | ]; clear -Hls Hvg; set_solver.
  - intros xl Hxl.
    change (has_context_type concrete_Φ ∅ (bst_left_tree_ctx n a u v g xp ls rs k xl)
      (bst_right_stage (vfvar g) (vfvar rs) (vfvar k) (vfvar xl))
      (CTUnder TTree (bst_result_qual {[u;v]} n a))).
    apply bst_right_stage_context_typed; assumption.
Qed.

Lemma bst_stage_pivot_ctx_wf n a u v g xp :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  wf_ctx_under ∅ (bst_pivot_ctx n a u v g xp).
Proof.
  intros Huv Hug Hvg Hxp. apply bst_positive_bind_wf.
  - apply bst_call_ctx_wf; assumption.
  - cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear -Hxp. set_solver.
  - unfold basic_context_ty,precise_ty,over_ty,under_ty.
    split; [|split; [|reflexivity]]; unfold bst_pivot_qual;
      apply param_result_qual_wf; cbn [ctx_dom bst_call_ctx nat_pair_ctx]; clear; set_solver.
Qed.

Lemma bst_stage_left_size_ctx_wf n a u v g xp ls :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) ->
  wf_ctx_under ∅ (bst_left_size_ctx n a u v g xp ls).
Proof.
  intros Huv Hug Hvg Hxp Hls. apply bst_positive_bind_wf.
  - apply bst_stage_pivot_ctx_wf; assumption.
  - cbn [ctx_dom bst_pivot_ctx bst_call_ctx nat_pair_ctx]. clear -Hls. set_solver.
  - unfold bst_pred_qual. apply param_result_qual_wf.
    cbn [ctx_dom bst_pivot_ctx bst_call_ctx nat_pair_ctx]. clear; set_solver.
Qed.

Lemma bst_stage_right_size_ctx_wf n a u v g xp ls rs :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  wf_ctx_under ∅ (bst_right_size_ctx n a u v g xp ls rs).
Proof.
  intros Huv Hug Hvg Hxp Hls Hrs. apply bst_positive_bind_wf.
  - apply bst_stage_left_size_ctx_wf; assumption.
  - cbn [ctx_dom bst_left_size_ctx bst_pivot_ctx bst_call_ctx nat_pair_ctx].
    clear -Hrs. set_solver.
  - rewrite q_nat_graph_free_param. apply param_result_qual_wf.
    cbn [ctx_dom bst_left_size_ctx bst_pivot_ctx bst_call_ctx nat_pair_ctx]. clear; set_solver.
Qed.

Local Ltac bst_prefix_lookup :=
  first [assumption | apply erase_ctx_comma_lookup_old; bst_prefix_lookup].

Lemma bst_stage_pivot_lookups n a u v g xp :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ (bst_pivot_ctx n a u v g xp) ->
  erase_ctx (bst_pivot_ctx n a u v g xp) !! u = Some (TBase TNat) /\
  erase_ctx (bst_pivot_ctx n a u v g xp) !! v = Some (TBase TNat) /\
  erase_ctx (bst_pivot_ctx n a u v g xp) !! g = Some BSTProgram.range_basic_ty /\
  erase_ctx (bst_pivot_ctx n a u v g xp) !! xp = Some (TBase TNat).
Proof.
  intros Huv Hug Hvg HΓ.
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g) xp
    (precise_ty TNat (bst_pivot_qual {[u;v]} n)) HΓ) as Hp.
  repeat split; bst_prefix_lookup.
Qed.

Lemma bst_stage_left_size_lookups n a u v g xp ls :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ (bst_left_size_ctx n a u v g xp ls) ->
  erase_ctx (bst_left_size_ctx n a u v g xp ls) !! u = Some (TBase TNat) /\
  erase_ctx (bst_left_size_ctx n a u v g xp ls) !! v = Some (TBase TNat) /\
  erase_ctx (bst_left_size_ctx n a u v g xp ls) !! g = Some BSTProgram.range_basic_ty /\
  erase_ctx (bst_left_size_ctx n a u v g xp ls) !! xp = Some (TBase TNat) /\
  erase_ctx (bst_left_size_ctx n a u v g xp ls) !! ls = Some (TBase TNat).
Proof.
  intros Huv Hug Hvg HΓ.
  destruct (bst_stage_pivot_lookups n a u v g xp Huv Hug Hvg (proj1 HΓ))
    as [Hu [Hv [Hg Hp]]].
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_pivot_ctx n a u v g xp) ls
    (CTOver TNat (bst_pred_qual xp)) HΓ) as Hls.
  repeat split; bst_prefix_lookup.
Qed.

Lemma bst_stage_right_size_lookups n a u v g xp ls rs :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ (bst_right_size_ctx n a u v g xp ls rs) ->
  erase_ctx (bst_right_size_ctx n a u v g xp ls rs) !! u = Some (TBase TNat) /\
  erase_ctx (bst_right_size_ctx n a u v g xp ls rs) !! v = Some (TBase TNat) /\
  erase_ctx (bst_right_size_ctx n a u v g xp ls rs) !! g = Some BSTProgram.range_basic_ty /\
  erase_ctx (bst_right_size_ctx n a u v g xp ls rs) !! xp = Some (TBase TNat) /\
  erase_ctx (bst_right_size_ctx n a u v g xp ls rs) !! ls = Some (TBase TNat) /\
  erase_ctx (bst_right_size_ctx n a u v g xp ls rs) !! rs = Some (TBase TNat).
Proof.
  intros Huv Hug Hvg HΓ.
  destruct (bst_stage_left_size_lookups n a u v g xp ls Huv Hug Hvg (proj1 HΓ))
    as [Hu [Hv [Hg [Hp Hls]]]].
  pose proof (erase_ctx_comma_lookup_new_wf ∅ (bst_left_size_ctx n a u v g xp ls) rs
    (CTOver TNat (q_nat_graph Nat.sub (LVFree u) (LVFree xp) (LVBound 0))) HΓ) as Hrs.
  repeat split; bst_prefix_lookup.
Qed.

Lemma bst_root_stage_context_typed n a u v g xp ls rs :
  0 < n -> u <> v -> u <> g -> v <> g ->
  xp ∉ ({[u;v;g]} : aset) -> ls ∉ ({[u;v;g;xp]} : aset) ->
  rs ∉ ({[u;v;g;xp;ls]} : aset) -> bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_right_size_ctx n a u v g xp ls rs)
    (bst_root_stage (vfvar v) (vfvar g) (vfvar xp) (vfvar ls) (vfvar rs))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hn Huv Hug Hvg Hxp Hls Hrs HIH.
  pose proof (bst_stage_right_size_ctx_wf n a u v g xp ls rs Huv Hug Hvg Hxp Hls Hrs) as HΓ.
  destruct (bst_stage_right_size_lookups n a u v g xp ls rs Huv Hug Hvg HΓ)
    as [Hu [Hv [Hg [Hp [Hsl Hsr]]]]].
  unfold bst_root_stage.
  eapply CT_Let with (τ1:=CTOver TNat (bst_root_qual {[u;v]} xp a))
    (L:=({[u;v;g;xp;ls;rs]} : aset)).
  - split; [exact HΓ|]. split.
    + apply bst_stage_result_wf; eassumption.
    + change (tm_has_type (erase_ctx (bst_right_size_ctx n a u v g xp ls rs))
        (bst_root_stage (vfvar v) (vfvar g) (vfvar xp) (vfvar ls) (vfvar rs)) (TBase TTree)).
      apply bst_root_stage_basic; assumption.
  - eapply bst_root_arithmetic_context_typed; try eassumption.
    + assert (HuD : u ∈ dom (erase_ctx (bst_right_size_ctx n a u v g xp ls rs)))
        by (apply elem_of_dom; eauto).
      assert (HvD : v ∈ dom (erase_ctx (bst_right_size_ctx n a u v g xp ls rs)))
        by (apply elem_of_dom; eauto).
      clear -HuD HvD. set_solver.
    + set_solver.
    + clear -Hxp. set_solver.
    + intros m σ Hctx Hσ.
      do 3 (apply ctx_denote_under_comma_left in Hctx).
      exact (proj2 (bst_call_ctx_lookup n a u v g m σ Hctx Hσ)).
  - intros k Hk.
    change (has_context_type concrete_Φ ∅ (bst_root_ctx n a u v g xp ls rs k)
      (bst_left_stage (vfvar v) (vfvar g) (vfvar ls) (vfvar rs) (vfvar k))
      (CTUnder TTree (bst_result_qual {[u;v]} n a))).
    apply bst_left_stage_context_typed; assumption.
Qed.

Lemma bst_sub_stage_context_typed n a u v g xp ls :
  0 < n -> u <> v -> u <> g -> v <> g ->
  xp ∉ ({[u;v;g]} : aset) -> ls ∉ ({[u;v;g;xp]} : aset) ->
  bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_left_size_ctx n a u v g xp ls)
    (bst_sub_stage (vfvar u) (vfvar v) (vfvar g) (vfvar xp) (vfvar ls))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hn Huv Hug Hvg Hxp Hls HIH.
  pose proof (bst_stage_left_size_ctx_wf n a u v g xp ls Huv Hug Hvg Hxp Hls) as HΓ.
  destruct (bst_stage_left_size_lookups n a u v g xp ls Huv Hug Hvg HΓ)
    as [Hu [Hv [Hg [Hp Hsl]]]].
  unfold bst_sub_stage.
  eapply CT_Let with
    (τ1:=CTOver TNat (q_nat_graph Nat.sub (LVFree u) (LVFree xp) (LVBound 0)))
    (L:=({[u;v;g;xp;ls]} : aset)).
  - split; [exact HΓ|]. split.
    + apply bst_stage_result_wf; eassumption.
    + change (tm_has_type (erase_ctx (bst_left_size_ctx n a u v g xp ls))
        (bst_sub_stage (vfvar u) (vfvar v) (vfvar g) (vfvar xp) (vfvar ls)) (TBase TTree)).
      apply bst_sub_stage_basic; assumption.
  - apply (arithmetic_app2_over_context_typed concrete_Φ _ false);
      try assumption. clear -Hxp. set_solver.
  - intros rs Hrs.
    change (has_context_type concrete_Φ ∅ (bst_right_size_ctx n a u v g xp ls rs)
      (bst_root_stage (vfvar v) (vfvar g) (vfvar xp) (vfvar ls) (vfvar rs))
      (CTUnder TTree (bst_result_qual {[u;v]} n a))).
    apply bst_root_stage_context_typed; assumption.
Qed.

Lemma bst_pred_stage_context_typed n a u v g xp :
  0 < n -> u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_pivot_ctx n a u v g xp)
    (bst_pred_stage (vfvar u) (vfvar v) (vfvar g) (vfvar xp))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hn Huv Hug Hvg Hxp HIH.
  pose proof (bst_stage_pivot_ctx_wf n a u v g xp Huv Hug Hvg Hxp) as HΓ.
  destruct (bst_stage_pivot_lookups n a u v g xp Huv Hug Hvg HΓ)
    as [Hu [Hv [Hg Hp]]].
  unfold bst_pred_stage.
  eapply CT_Let with (τ1:=CTOver TNat (bst_pred_qual xp))
    (L:=({[u;v;g;xp]} : aset)).
  - split; [exact HΓ|]. split.
    + apply bst_stage_result_wf; eassumption.
    + change (tm_has_type (erase_ctx (bst_pivot_ctx n a u v g xp))
        (bst_pred_stage (vfvar u) (vfvar v) (vfvar g) (vfvar xp)) (TBase TTree)).
      apply bst_pred_stage_basic; assumption.
  - apply bst_pred_primitive_context_typed; assumption.
  - intros ls Hls.
    change (has_context_type concrete_Φ ∅ (bst_left_size_ctx n a u v g xp ls)
      (bst_sub_stage (vfvar u) (vfvar v) (vfvar g) (vfvar xp) (vfvar ls))
      (CTUnder TTree (bst_result_qual {[u;v]} n a))).
    apply bst_sub_stage_context_typed; assumption.
Qed.

Lemma bst_generate_stage_context_typed n a u v g :
  0 < n -> u <> v -> u <> g -> v <> g -> bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_call_ctx n a u v g)
    (bst_generate_stage (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hn Huv Hug Hvg HIH.
  pose proof (bst_call_ctx_wf n a u v g Huv Hug Hvg) as HΓ.
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  unfold bst_generate_stage.
  eapply CT_Let with (τ1:=precise_ty TNat (bst_pivot_qual {[u;v]} n))
    (L:=({[u;v;g]} : aset)).
  - split; [exact HΓ|]. split.
    + apply bst_stage_result_wf; eassumption.
    + change (tm_has_type (erase_ctx (bst_call_ctx n a u v g))
        (bst_generate_stage (vfvar u) (vfvar v) (vfvar g)) (TBase TTree)).
      apply bst_generate_stage_basic; assumption.
  - apply bst_range_call_context_typed; assumption.
  - intros xp Hxp.
    change (has_context_type concrete_Φ ∅ (bst_pivot_ctx n a u v g xp)
      (bst_pred_stage (vfvar u) (vfvar v) (vfvar g) (vfvar xp))
      (CTUnder TTree (bst_result_qual {[u;v]} n a))).
    apply bst_pred_stage_context_typed; assumption.
Qed.

Lemma bst_choose_basic Δ left right T :
  tm_has_type Δ left T -> tm_has_type Δ right T ->
  tm_has_type Δ (choose_tm left right) T.
Proof.
  intros Hl Hr.
  pose proof (typing_tm_lc _ _ _ Hl) as Hlcl.
  pose proof (typing_tm_lc _ _ _ Hr) as Hlcr.
  unfold choose_tm. rewrite !tm_shift_lc_id by assumption.
  eapply TT_Let with (L:=dom Δ).
  - eapply TT_Op; [reflexivity|apply VT_Const].
  - intros x Hx.
    change (tm_has_type (<[x:=TBase TBool]> Δ)
      (open_tm 0 (vfvar x) (tmatch (vbvar 0) left right)) T).
    rewrite choose_body_open by assumption.
    apply TT_Match.
    + apply VT_FVar. apply map_lookup_insert.
    + eapply basic_typing_weaken_tm; [exact Hl|]. apply insert_subseteq. apply not_elem_of_dom. exact Hx.
    + eapply basic_typing_weaken_tm; [exact Hr|]. apply insert_subseteq. apply not_elem_of_dom. exact Hx.
Qed.

Lemma bst_leaf_over_top_context_typed Φ Σ Γ :
  wf_ctx_under Σ Γ ->
  has_context_type Φ Σ Γ (tret (vconst (ctree tr_leaf))) (CTOver TTree qual_top).
Proof.
  intros HΓ.
  assert (Htop : wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTOver TTree qual_top)).
  { eapply wf_context_ty_at_mono_env; [|apply (over_top_basic TTree)]. set_solver. }
  eapply CT_Sub with (τ1:=const_precise_ty (ctree tr_leaf)).
  - split; [exact HΓ|]. split; [exact Htop|apply TT_Ret,VT_Const].
  - apply typing_const_in_ctx. split; [exact HΓ|].
    split; [apply const_precise_wf|apply TT_Ret,VT_Const].
  - apply sub_type_under_intro; [exact HΓ|apply const_precise_wf|exact Htop|reflexivity|].
    intros e m He Hctx Hsource.
    pose proof (ty_denote_under_total Σ Γ _ e m Hsource) as Htotal.
    unfold ty_denote_under,ty_denote.
    apply over_top_denotation_gas.
    apply ty_guard_relevant_of_static_full_total; [|exact Htotal].
    eapply context_typing_wf_denot_static_guard_full; [|exact Hctx].
    split; [exact HΓ|]. split; assumption.
Qed.

Lemma bst_positive_branch_context_typed n a u v g :
  0 < n -> u <> v -> u <> g -> v <> g -> bst_smaller_calls_typed n ->
  has_context_type concrete_Φ ∅ (bst_call_ctx n a u v g)
    (bst_positive_branch (vfvar u) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0))).
Proof.
  intros Hn Huv Hug Hvg HIH.
  pose proof (bst_call_ctx_wf n a u v g Huv Hug Hvg) as HΓ.
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  assert (HuD : u ∈ dom (erase_ctx (bst_call_ctx n a u v g))) by (apply elem_of_dom; eauto).
  assert (HvD : v ∈ dom (erase_ctx (bst_call_ctx n a u v g))) by (apply elem_of_dom; eauto).
  pose proof (bst_generate_stage_context_typed n a u v g Hn Huv Hug Hvg HIH) as Hgenerate.
  pose proof (context_typing_wf_basic_typing _ _ _ _ (typing_wf_under _ _ _ _ _ Hgenerate)) as Hbasic.
  rewrite bst_positive_branch_generate.
  change (has_context_type concrete_Φ ∅ (bst_call_ctx n a u v g)
    (choose_tm (tret (vconst (ctree tr_leaf))) (bst_generate_stage (vfvar u) (vfvar v) (vfvar g)))
    (CTUnder TTree (q_tree_bst_range (vfvar u) (vfvar v) (vbvar 0)))).
  eapply CT_Sub with (τ1:=CTUnder TTree (bst_result_qual {[u;v]} n a)).
  - split; [exact HΓ|]. split.
    + apply q_bst_free_wf; assumption.
    + apply bst_choose_basic; [apply TT_Ret,VT_Const|exact Hbasic].
  - apply CT_ChooseUnder.
    + split; [exact HΓ|]. split.
      * apply bst_stage_result_wf; eassumption.
      * apply bst_choose_basic; [apply TT_Ret,VT_Const|exact Hbasic].
    + apply bst_leaf_over_top_context_typed. exact HΓ.
    + exact Hgenerate.
  - apply bst_result_to_free_subtype; try assumption.
    intros m σ Hctx Hσ. exact (bst_call_ctx_lookup n a u v g m σ Hctx Hσ).
Qed.
