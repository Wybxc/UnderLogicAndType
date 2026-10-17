(** The original positive branch, with dependent bindings in program order. *)
From CaseStudy Require Import BSTContext BSTNodeTypes BSTArithmeticSupport
  BSTRecursiveCases BSTRightRecursiveCases NatArithmeticTyping BSTGeneratorUnfolding
  NatArithmetic BSTGeneratorProgram.
From Denotation Require Import Context ConditionalCoverage ResultQualifier QualifierStore.
From ContextTyping Require Import Typing BasicBindings Subtyping OverConsequence NatCases Weakening.

Lemma bst_comma_over_store Σ Γ x b φ (m : WfWorldT) :
  x ∉ qual_dom φ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x (CTOver b φ))) ->
  forall σ, (m : WorldT) σ ->
    qualifier_holds_store (qual_open_atom 0 x (typed_result_qual b φ)) σ.
Proof.
  intros Hx Hctx.
  cbn [ctx_denote_under] in Hctx.
  apply res_models_and_iff in Hctx as [_ Hbody].
  apply res_models_and_iff in Hbody as [_ Hbind].
  apply res_models_and_iff in Hbind as [_ Hden].
  eapply (over_ret_var_store_holds 0 _ b φ x m);
    [apply atom_store_to_lvar_store_closed|exact Hx|exact Hden].
Qed.

Lemma bst_comma_precise_store Σ Γ x b φ (m : WfWorldT) :
  x ∉ qual_dom φ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x (precise_ty b φ))) ->
  forall σ, (m : WorldT) σ ->
    qualifier_holds_store (qual_open_atom 0 x (typed_result_qual b φ)) σ.
Proof.
  intros Hx Hctx.
  cbn [ctx_denote_under] in Hctx.
  apply res_models_and_iff in Hctx as [_ Hbody].
  apply res_models_and_iff in Hbody as [_ Hbind].
  apply res_models_and_iff in Hbind as [_ Hden].
  cbn [ty_denote cty_depth precise_ty ty_denote_gas] in Hden.
  apply res_models_and_iff in Hden as [_ Hparts].
  apply res_models_and_iff in Hparts as [Hover _].
  eapply (over_ret_var_store_holds 0 _ b φ x m);
    [apply atom_store_to_lvar_store_closed|exact Hx|exact Hover].
Qed.

Definition bst_pivot_ctx n a u v g xp : ctx :=
  CtxComma (bst_call_ctx n a u v g)
    (CtxBind xp (precise_ty TNat (bst_pivot_qual {[u;v]} n))).
Definition bst_left_size_ctx n a u v g xp ls : ctx :=
  CtxComma (bst_pivot_ctx n a u v g xp)
    (CtxBind ls (CTOver TNat (bst_pred_qual xp))).
Definition bst_right_size_ctx n a u v g xp ls rs : ctx :=
  CtxComma (bst_left_size_ctx n a u v g xp ls)
    (CtxBind rs (CTOver TNat
      (q_nat_graph Nat.sub (LVFree u) (LVFree xp) (LVBound 0)))).
Definition bst_root_ctx n a u v g xp ls rs k : ctx :=
  CtxComma (bst_right_size_ctx n a u v g xp ls rs)
    (CtxBind k (CTOver TNat (bst_root_qual {[u;v]} xp a))).
Definition bst_left_tree_ctx n a u v g xp ls rs k xl : ctx :=
  CtxComma (bst_root_ctx n a u v g xp ls rs k)
    (CtxBind xl (CTUnder TTree (bst_left_qual {[u;v]} xp n a))).
Definition bst_right_tree_ctx n a u v g xp ls rs k xl xr : ctx :=
  CtxComma (bst_left_tree_ctx n a u v g xp ls rs k xl)
    (CtxBind xr (CTUnder TTree (bst_right_qual {[u;v]} xp xl n a))).

Lemma bst_pivot_ctx_lookup n a u v g xp (m : WfWorldT) σ :
  xp ∉ ({[u;v]} : aset) ->
  m ⊨ ctx_denote_under ∅ (bst_pivot_ctx n a u v g xp) -> (m : WorldT) σ ->
  σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\
  exists p, 1 <= p <= n /\ σ !! xp = Some (vnat p).
Proof.
  intros Hxp Hctx Hσ.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hbase.
  destruct (bst_call_ctx_lookup n a u v g m σ Hbase Hσ) as [Hu Hv].
  pose proof (bst_comma_precise_store ∅ (bst_call_ctx n a u v g) xp TNat
    (bst_pivot_qual {[u;v]} n) m
    ltac:(unfold bst_pivot_qual; rewrite param_result_qual_dom; exact Hxp) Hctx σ Hσ) as Hq.
  unfold bst_pivot_qual in Hq.
  apply typed_param_result_qual_open_store in Hq; [|exact Hxp].
  destruct Hq as [_ [w [Hpw [_ [p [-> Hp]]]]]].
  split; [exact Hu|]. split; [exact Hv|]. exists p. auto.
Qed.

Lemma bst_left_size_ctx_lookup n a u v g xp ls (m : WfWorldT) σ :
  xp ∉ ({[u;v]} : aset) -> ls <> xp ->
  m ⊨ ctx_denote_under ∅ (bst_left_size_ctx n a u v g xp ls) -> (m : WorldT) σ ->
  σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\
  exists p, 1 <= p <= n /\ σ !! xp = Some (vnat p) /\ σ !! ls = Some (vnat (p-1)).
Proof.
  intros Hxp Hls Hctx Hσ.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hprev.
  destruct (bst_pivot_ctx_lookup n a u v g xp m σ Hxp Hprev Hσ)
    as [Hu [Hv [p [Hp Hpv]]]].
  pose proof (bst_comma_over_store ∅ (bst_pivot_ctx n a u v g xp) ls TNat
    (bst_pred_qual xp) m
    ltac:(unfold bst_pred_qual; rewrite param_result_qual_dom;
      clear -Hls; set_solver) Hctx σ Hσ) as Hq.
  unfold bst_pred_qual in Hq.
  apply typed_param_result_qual_open_store in Hq; [|clear -Hls; set_solver].
  destruct Hq as [_ [w [Hlsw [_ [p' [Hpv' ->]]]]]].
  rewrite store_restrict_lookup_at in Hpv' by set_solver.
  assert (Heq : p'=p).
  { assert (Hsame : Some (vnat p') = Some (vnat p)).
    { transitivity (σ !! xp); [symmetry; exact Hpv'|exact Hpv]. }
    now inversion Hsame. }
  subst p'. split; [exact Hu|]. split; [exact Hv|]. exists p. auto.
Qed.

Lemma bst_positive_bind_wf Σ Γ x τ :
  wf_ctx_under Σ Γ -> x ∉ dom Σ ∪ ctx_dom Γ ->
  basic_context_ty (dom Σ ∪ ctx_dom Γ) τ ->
  wf_ctx_under Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros HΓ Hx Hτ. split; [exact HΓ|]. split.
  - split; assumption.
  - cbn [ctx_dom]. clear -Hx. set_solver.
Qed.

Lemma bst_root_ctx_wf n a u v g xp ls rs k :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  k ∉ ({[u;v;g;xp;ls;rs]} : aset) ->
  wf_ctx_under ∅ (bst_root_ctx n a u v g xp ls rs k).
Proof.
  intros Huv Hug Hvg Hxp Hls Hrs Hk.
  unfold bst_root_ctx,bst_right_size_ctx,bst_left_size_ctx,bst_pivot_ctx.
  apply bst_positive_bind_wf.
  - apply bst_positive_bind_wf.
    + apply bst_positive_bind_wf.
      * apply bst_positive_bind_wf.
        -- apply bst_call_ctx_wf; assumption.
        -- cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear -Hxp. set_solver.
        -- unfold basic_context_ty,precise_ty,over_ty,under_ty.
           split; [|split; [|reflexivity]];
             unfold bst_pivot_qual; apply param_result_qual_wf;
             cbn [ctx_dom bst_call_ctx nat_pair_ctx]; clear; set_solver.
      * cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear -Hls. set_solver.
      * unfold bst_pred_qual. apply param_result_qual_wf.
        cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear; set_solver.
    + cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear -Hrs. set_solver.
    + rewrite q_nat_graph_free_param. apply param_result_qual_wf.
      cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear; set_solver.
  - cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear -Hk. set_solver.
  - unfold bst_root_qual. apply param_result_qual_wf.
    cbn [ctx_dom bst_call_ctx nat_pair_ctx]. clear; set_solver.
Qed.

Lemma bst_left_tree_ctx_wf n a u v g xp ls rs k xl :
  wf_ctx_under ∅ (bst_root_ctx n a u v g xp ls rs k) ->
  xl ∉ ({[u;v;g;xp;ls;rs;k]} : aset) ->
  wf_ctx_under ∅ (bst_left_tree_ctx n a u v g xp ls rs k xl).
Proof.
  intros HΓ Hxl. apply bst_positive_bind_wf; [exact HΓ| |].
  - cbn [ctx_dom bst_root_ctx bst_right_size_ctx bst_left_size_ctx bst_pivot_ctx
      bst_call_ctx nat_pair_ctx]. clear -Hxl. set_solver.
  - unfold bst_left_qual. apply param_result_qual_wf.
    cbn [ctx_dom bst_root_ctx bst_right_size_ctx bst_left_size_ctx bst_pivot_ctx
      bst_call_ctx nat_pair_ctx]. clear; set_solver.
Qed.

Lemma bst_right_tree_ctx_wf n a u v g xp ls rs k xl xr :
  wf_ctx_under ∅ (bst_left_tree_ctx n a u v g xp ls rs k xl) ->
  xr ∉ ({[u;v;g;xp;ls;rs;k;xl]} : aset) ->
  wf_ctx_under ∅ (bst_right_tree_ctx n a u v g xp ls rs k xl xr).
Proof.
  intros HΓ Hxr. apply bst_positive_bind_wf; [exact HΓ| |].
  - cbn [ctx_dom bst_left_tree_ctx bst_root_ctx bst_right_size_ctx bst_left_size_ctx
      bst_pivot_ctx bst_call_ctx nat_pair_ctx]. clear -Hxr. set_solver.
  - unfold bst_right_qual. apply param_result_qual_wf.
    cbn [ctx_dom bst_left_tree_ctx bst_root_ctx bst_right_size_ctx bst_left_size_ctx
      bst_pivot_ctx bst_call_ctx nat_pair_ctx]. clear; set_solver.
Qed.

Lemma bst_right_size_ctx_lookup n a u v g xp ls rs (m : WfWorldT) σ :
  xp ∉ ({[u;v]} : aset) -> ls <> xp -> rs ∉ ({[u;xp]} : aset) ->
  m ⊨ ctx_denote_under ∅ (bst_right_size_ctx n a u v g xp ls rs) -> (m : WorldT) σ ->
  σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\
  exists p, 1 <= p <= n /\ σ !! xp = Some (vnat p) /\
    σ !! ls = Some (vnat (p-1)) /\ σ !! rs = Some (vnat (n-p)).
Proof.
  intros Hxp Hls Hrs Hctx Hσ.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hprev.
  destruct (bst_left_size_ctx_lookup n a u v g xp ls m σ Hxp Hls Hprev Hσ)
    as [Hu [Hv [p [Hp [Hpv Hlsv]]]]].
  pose proof (bst_comma_over_store ∅ (bst_left_size_ctx n a u v g xp ls) rs TNat
    (q_nat_graph Nat.sub (LVFree u) (LVFree xp) (LVBound 0)) m
    ltac:(rewrite q_nat_graph_free_param,param_result_qual_dom; exact Hrs)
    Hctx σ Hσ) as Hq.
  rewrite q_nat_graph_free_param in Hq.
  apply typed_param_result_qual_open_store in Hq; [|exact Hrs].
  destruct Hq as [_ [w [Hrsw [_ [n' [p' [Hu' [Hpv' ->]]]]]]]].
  rewrite !store_restrict_lookup_at in Hu',Hpv' by (clear; set_solver).
  assert (Hn : n'=n).
  { assert (Hsame : Some (vnat n') = Some (vnat n)).
    { transitivity (σ !! u); [symmetry; exact Hu'|exact Hu]. }
    now inversion Hsame. }
  assert (Hp' : p'=p).
  { assert (Hsame : Some (vnat p') = Some (vnat p)).
    { transitivity (σ !! xp); [symmetry; exact Hpv'|exact Hpv]. }
    now inversion Hsame. }
  subst n' p'. split; [exact Hu|]. split; [exact Hv|]. exists p. auto.
Qed.

Lemma bst_root_ctx_lookup n a u v g xp ls rs k (m : WfWorldT) σ :
  xp ∉ ({[u;v]} : aset) -> ls <> xp -> rs ∉ ({[u;xp]} : aset) ->
  k ∉ ({[u;v]} ∪ {[xp]} : aset) ->
  m ⊨ ctx_denote_under ∅ (bst_root_ctx n a u v g xp ls rs k) -> (m : WorldT) σ ->
  σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\
  exists p, 1 <= p <= n /\ σ !! xp = Some (vnat p) /\
    σ !! ls = Some (vnat (p-1)) /\ σ !! rs = Some (vnat (n-p)) /\
    σ !! k = Some (vnat (a+p)).
Proof.
  intros Hxp Hls Hrs Hk Hctx Hσ.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hprev.
  destruct (bst_right_size_ctx_lookup n a u v g xp ls rs m σ Hxp Hls Hrs Hprev Hσ)
    as [Hu [Hv [p [Hp [Hpv [Hlsv Hrsv]]]]]].
  pose proof (bst_comma_over_store ∅ (bst_right_size_ctx n a u v g xp ls rs) k TNat
    (bst_root_qual {[u;v]} xp a) m
    ltac:(unfold bst_root_qual; rewrite param_result_qual_dom; exact Hk)
    Hctx σ Hσ) as Hq.
  unfold bst_root_qual in Hq.
  apply typed_param_result_qual_open_store in Hq; [|exact Hk].
  destruct Hq as [_ [w [Hkw [_ [p' [k' [Hpv' [-> ->]]]]]]]].
  rewrite store_restrict_lookup_at in Hpv' by (clear; set_solver).
  assert (Hp' : p'=p).
  { assert (Hsame : Some (vnat p') = Some (vnat p)).
    { transitivity (σ !! xp); [symmetry; exact Hpv'|exact Hpv]. }
    now inversion Hsame. }
  subst p'. split; [exact Hu|]. split; [exact Hv|]. exists p. auto.
Qed.

Lemma bst_left_call_positive_context_typed Φ n a u v g xp ls rs k :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  k ∉ ({[u;v;g;xp;ls;rs]} : aset) ->
  (forall p, 1 <= p <= n -> p-1<n ->
    has_context_type Φ ∅ (bst_call_ctx (p-1) a ls v g)
      (NatArithmetic.app3 bst_gen_value (vfvar ls) (vfvar v) (vfvar g))
      (CTUnder TTree (q_tree_bst_range (vfvar ls) (vfvar v) (vbvar 0)))) ->
  has_context_type Φ ∅ (bst_root_ctx n a u v g xp ls rs k)
    (NatArithmetic.app3 bst_gen_value (vfvar ls) (vfvar v) (vfvar g))
    (CTUnder TTree (bst_left_qual {[u;v]} xp n a)).
Proof.
  intros Huv Hug Hvg Hxp Hls Hrs Hk HIH.
  pose proof (bst_root_ctx_wf n a u v g xp ls rs k Huv Hug Hvg Hxp Hls Hrs Hk) as HΓ.
  pose proof (bst_left_case_ctx_wf n a 0 u v g xp ls rs k
    Huv Hug Hvg Hxp Hls Hrs Hk) as Hcase.
  destruct (bst_left_case_erasure_lookups n a 0 u v g xp ls rs k
    Huv Hug Hvg Hcase) as [Hu [Hv [Hg [Hp [Hsl [Hsr Hkr]]]]]].
  eapply bst_left_recursive_context_typed; try eassumption.
  - split; [exact HΓ|]. split.
    + unfold bst_left_qual. apply param_result_qual_wf.
      assert (HuD : u ∈ dom (erase_ctx (bst_root_ctx n a u v g xp ls rs k)))
        by (apply elem_of_dom; exists (TBase TNat); exact Hu).
      assert (HvD : v ∈ dom (erase_ctx (bst_root_ctx n a u v g xp ls rs k)))
        by (apply elem_of_dom; exists (TBase TNat); exact Hv).
      assert (HpD : xp ∈ dom (erase_ctx (bst_root_ctx n a u v g xp ls rs k)))
        by (apply elem_of_dom; exists (TBase TNat); exact Hp).
      clear -HuD HvD HpD. set_solver.
    + apply bst_call_variables_basic_typed; assumption.
  - intros p. reflexivity.
  - intros m Hctx.
    do 4 (apply ctx_denote_under_comma_left in Hctx).
    exact (proj2 (proj2 (bst_call_ctx_denote_inv n a u v g m Hctx))).
  - intros m σ Hctx Hσ.
    destruct (bst_root_ctx_lookup n a u v g xp ls rs k m σ
      ltac:(clear -Hxp; set_solver) ltac:(clear -Hls; set_solver)
      ltac:(clear -Hrs; set_solver) ltac:(clear -Hk; set_solver) Hctx Hσ)
      as [Hnu [Hav [p [Hlegal [Hpv [Hlsv _]]]]]].
    split; [exact Hnu|]. split; [exact Hav|]. exists p. auto.
Qed.

Lemma bst_right_call_positive_context_typed Φ n a u v g xp ls rs k xl :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  k ∉ ({[u;v;g;xp;ls;rs]} : aset) -> xl ∉ ({[u;v;g;xp;ls;rs;k]} : aset) ->
  (forall p, 1 <= p <= n -> n-p<n ->
    has_context_type Φ ∅ (bst_call_ctx (n-p) (a+p) rs k g)
      (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g))
      (CTUnder TTree (q_tree_bst_range (vfvar rs) (vfvar k) (vbvar 0)))) ->
  has_context_type Φ ∅ (bst_left_tree_ctx n a u v g xp ls rs k xl)
    (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g))
    (CTUnder TTree (bst_right_qual {[u;v]} xp xl n a)).
Proof.
  intros Huv Hug Hvg Hxp Hls Hrs Hk Hxl HIH.
  pose proof (bst_root_ctx_wf n a u v g xp ls rs k Huv Hug Hvg Hxp Hls Hrs Hk) as HrΓ.
  pose proof (bst_left_tree_ctx_wf n a u v g xp ls rs k xl HrΓ Hxl) as HΓ.
  pose proof (bst_right_case_ctx_wf n a 0 tr_leaf u v g xp ls rs k xl
    Huv Hug Hvg Hxp Hls Hrs Hk Hxl) as Hcase.
  destruct (bst_right_case_erasure_lookups n a 0 tr_leaf u v g xp ls rs k xl
    Huv Hug Hvg Hcase) as [Hu [Hv [Hg [Hp [Hsl [Hsr [Hkr Hlt]]]]]]].
  eapply bst_right_recursive_context_typed; try eassumption.
  - split; [exact HΓ|]. split.
    + unfold bst_right_qual. apply param_result_qual_wf.
      assert (HuD : u ∈ dom (erase_ctx (bst_left_tree_ctx n a u v g xp ls rs k xl)))
        by (apply elem_of_dom; exists (TBase TNat); exact Hu).
      assert (HvD : v ∈ dom (erase_ctx (bst_left_tree_ctx n a u v g xp ls rs k xl)))
        by (apply elem_of_dom; exists (TBase TNat); exact Hv).
      assert (HpD : xp ∈ dom (erase_ctx (bst_left_tree_ctx n a u v g xp ls rs k xl)))
        by (apply elem_of_dom; exists (TBase TNat); exact Hp).
      assert (HlD : xl ∈ dom (erase_ctx (bst_left_tree_ctx n a u v g xp ls rs k xl)))
        by (apply elem_of_dom; exists (TBase TTree); exact Hlt).
      clear -HuD HvD HpD HlD. set_solver.
    + apply bst_call_variables_basic_typed; assumption.
  - intros p t. reflexivity.
  - intros m Hctx.
    do 5 (apply ctx_denote_under_comma_left in Hctx).
    exact (proj2 (proj2 (bst_call_ctx_denote_inv n a u v g m Hctx))).
  - intros m σ Hctx Hσ.
    pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hroot.
    destruct (bst_root_ctx_lookup n a u v g xp ls rs k m σ
      ltac:(clear -Hxp; set_solver) ltac:(clear -Hls; set_solver)
      ltac:(clear -Hrs; set_solver) ltac:(clear -Hk; set_solver) Hroot Hσ)
      as [Hnu [Hav [p [Hlegal [Hpv [_ [Hrsv Hkv]]]]]]].
    destruct (ctx_denote_under_lookup_typed ∅ _ xl _ m σ HΓ Hlt Hctx Hσ)
      as [vl [Hvl Hvlty]].
    destruct (basic_typing_tree_canonical_form _ Hvlty) as [t ->].
    split; [exact Hnu|]. split; [exact Hav|]. exists p,t. auto.
Qed.

Lemma bst_positive_node_context_typed Φ n a u v g xp ls rs k xl xr :
  0 < n -> u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  k ∉ ({[u;v;g;xp;ls;rs]} : aset) -> xl ∉ ({[u;v;g;xp;ls;rs;k]} : aset) ->
  xr ∉ ({[u;v;g;xp;ls;rs;k;xl]} : aset) ->
  has_context_type Φ ∅ (bst_right_tree_ctx n a u v g xp ls rs k xl xr)
    (tnode (vfvar k) (vfvar xl) (vfvar xr))
    (CTUnder TTree (bst_result_qual {[u;v]} n a)).
Proof.
  intros Hn Huv Hug Hvg Hxp Hls Hrs Hk Hxl Hxr.
  pose proof (bst_root_ctx_wf n a u v g xp ls rs k Huv Hug Hvg Hxp Hls Hrs Hk) as Hw4.
  pose proof (bst_left_tree_ctx_wf n a u v g xp ls rs k xl Hw4 Hxl) as Hw5.
  pose proof (bst_right_tree_ctx_wf n a u v g xp ls rs k xl xr Hw5 Hxr) as Hw6.
  pose proof (proj1 Hw4) as Hw3. pose proof (proj1 Hw3) as Hw2.
  pose proof (proj1 Hw2) as Hw1.
  pose proof (bst_right_case_ctx_wf n a 0 tr_leaf u v g xp ls rs k xl
    Huv Hug Hvg Hxp Hls Hrs Hk Hxl) as Hcase.
  destruct (bst_right_case_erasure_lookups n a 0 tr_leaf u v g xp ls rs k xl
    Huv Hug Hvg Hcase) as [Hu [Hv [Hg [Hp [Hsl [Hsr [Hkr Hlt]]]]]]].
  assert (Hk6 : erase_ctx (bst_right_tree_ctx n a u v g xp ls rs k xl xr) !! k =
    Some (TBase TNat)) by (apply erase_ctx_comma_lookup_old; exact Hkr).
  assert (Hl6 : erase_ctx (bst_right_tree_ctx n a u v g xp ls rs k xl xr) !! xl =
    Some (TBase TTree)) by (apply erase_ctx_comma_lookup_old; exact Hlt).
  assert (Hr6 : erase_ctx (bst_right_tree_ctx n a u v g xp ls rs k xl xr) !! xr =
    Some (TBase TTree)).
  { exact (erase_ctx_comma_lookup_new_wf ∅ (bst_left_tree_ctx n a u v g xp ls rs k xl)
      xr (CTUnder TTree (bst_right_qual {[u;v]} xp xl n a)) Hw6). }
  eapply (bst_node_context_typed Φ ∅ _ n a {[u;v]} xp k xl xr);
    [exact Hn| | | | | | | | |].
  - clear -Hxp. set_solver.
  - clear -Hk. set_solver.
  - clear -Hxl. set_solver.
  - clear -Hxr. set_solver.
  - split; [exact Hw6|]. split.
    + unfold bst_result_qual. apply param_result_qual_wf.
      assert (HuD : u ∈ dom (erase_ctx (bst_right_tree_ctx n a u v g xp ls rs k xl xr))).
      { apply elem_of_dom. exists (TBase TNat). apply erase_ctx_comma_lookup_old. exact Hu. }
      assert (HvD : v ∈ dom (erase_ctx (bst_right_tree_ctx n a u v g xp ls rs k xl xr))).
      { apply elem_of_dom. exists (TBase TNat). apply erase_ctx_comma_lookup_old. exact Hv. }
      clear -HuD HvD. set_solver.
    + apply TT_TreeNode; apply VT_FVar; assumption.
  - apply typing_inter_r with (τ1:=CTOver TNat (bst_pivot_qual {[u;v]} n)).
    do 5 (apply typing_comma_prefix_wf; [assumption|]).
    apply typing_var_right_wf. exact Hw1.
  - do 2 (apply typing_comma_prefix_wf; [assumption|]).
    apply typing_var_right_wf. exact Hw4.
  - apply typing_comma_prefix_wf; [exact Hw6|].
    apply typing_var_right_wf. exact Hw5.
  - apply typing_var_right_wf. exact Hw6.
Qed.
