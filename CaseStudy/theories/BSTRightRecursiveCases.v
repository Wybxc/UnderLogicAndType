(** Right recursive calls are classified by pivot and the actual left tree.
    Every left tree is admitted; no completeness condition is imposed on it. *)
From CaseStudy Require Import BSTContext BSTSupport BSTNodeTypes BSTRecursiveSupport
  BSTGeneratorProgram BSTGeneratorUnfolding NatArithmetic.
From Denotation Require Import Context ResultQualifier QualifierStore.
From ContextTyping Require Import Typing TypingRegular BasicBindings ConstCases
  NatCases Subtyping FiberSupport.

Definition bst_right_case_prefix_ctx n a p u v g xp ls rs k : ctx :=
  CtxComma
    (CtxComma
      (CtxComma
        (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p)))
        (CtxBind ls nat_over_ty))
      (CtxBind rs (nat_singleton_ty (n-p))))
    (CtxBind k (nat_singleton_ty (a+p))).

Definition bst_right_case_ctx n a p t u v g xp ls rs k xl : ctx :=
  CtxComma (bst_right_case_prefix_ctx n a p u v g xp ls rs k)
    (CtxBind xl (const_precise_ty (ctree t))).

Lemma bst_right_case_ctx_wf n a p t u v g xp ls rs k xl :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  k ∉ ({[u;v;g;xp;ls;rs]} : aset) -> xl ∉ ({[u;v;g;xp;ls;rs;k]} : aset) ->
  wf_ctx_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl).
Proof.
  intros Huv Hug Hvg Hxp Hls Hrs Hk Hxl.
  unfold bst_right_case_ctx,bst_right_case_prefix_ctx.
  do 5 (apply wf_ctx_comma_closed_bind;
    [|cbn [ctx_dom bst_call_ctx nat_pair_ctx]; set_solver|
     first [apply nat_over_wf|apply nat_singleton_wf|apply const_precise_wf]]).
  apply bst_call_ctx_wf; assumption.
Qed.

Lemma bst_right_case_ctx_denote_intro n a p t u v g xp ls rs k xl (m : WfWorldT) :
  wf_ctx_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl) ->
  m ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g) ->
  m ⊨ ctx_denote_under ∅ (CtxBind xp (nat_singleton_ty p)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind ls nat_over_ty) ->
  m ⊨ ctx_denote_under ∅ (CtxBind rs (nat_singleton_ty (n-p))) ->
  m ⊨ ctx_denote_under ∅ (CtxBind k (nat_singleton_ty (a+p))) ->
  m ⊨ ctx_denote_under ∅ (CtxBind xl (const_precise_ty (ctree t))) ->
  m ⊨ ctx_denote_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl).
Proof.
  intros Hwf Hbase Hxp Hls Hrs Hk Hxl.
  unfold bst_right_case_ctx,bst_right_case_prefix_ctx in Hwf |- *.
  pose proof (proj1 Hwf) as Hw4.
  pose proof (proj1 Hw4) as Hw3.
  pose proof (proj1 Hw3) as Hw2.
  pose proof (proj1 Hw2) as Hw1.
  apply ctx_denote_under_comma_intro; [exact Hw4| |].
  2: { rewrite ctx_denote_closed_env; [exact Hxl|apply const_precise_fv]. }
  apply ctx_denote_under_comma_intro; [exact Hw3| |].
  2: { rewrite ctx_denote_closed_env; [exact Hk|apply nat_singleton_fv]. }
  apply ctx_denote_under_comma_intro; [exact Hw2| |].
  2: { rewrite ctx_denote_closed_env; [exact Hrs|apply nat_singleton_fv]. }
  apply ctx_denote_under_comma_intro; [exact Hw1| |].
  2: { rewrite ctx_denote_closed_env; [exact Hls|apply nat_over_fv]. }
  apply ctx_denote_under_comma_intro; [exact (proj1 Hw1)|exact Hbase|].
  rewrite ctx_denote_closed_env; [exact Hxp|apply nat_singleton_fv].
Qed.

Lemma bst_right_case_ctx_denote_inv n a p t u v g xp ls rs k xl (m : WfWorldT) :
  m ⊨ ctx_denote_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl) ->
  m ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g) /\
  m ⊨ ctx_denote_under ∅ (CtxBind xp (nat_singleton_ty p)) /\
  m ⊨ ctx_denote_under ∅ (CtxBind rs (nat_singleton_ty (n-p))) /\
  m ⊨ ctx_denote_under ∅ (CtxBind k (nat_singleton_ty (a+p))) /\
  m ⊨ ctx_denote_under ∅ (CtxBind xl (const_precise_ty (ctree t))).
Proof.
  intros Hctx. unfold bst_right_case_ctx,bst_right_case_prefix_ctx in Hctx.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hk.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hk) as Hrs.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hrs) as Hls.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hls) as Hxp.
  split; [exact (ctx_denote_under_comma_left ∅ _ _ m Hxp)|].
  split; [eapply ctx_denote_comma_closed_right;
    [apply nat_singleton_fv|exact Hxp]|].
  split; [eapply ctx_denote_comma_closed_right;
    [apply nat_singleton_fv|exact Hrs]|].
  split; [eapply ctx_denote_comma_closed_right;
    [apply nat_singleton_fv|exact Hk]|].
  eapply ctx_denote_comma_closed_right; [|exact Hctx].
  apply const_precise_fv.
Qed.

Lemma bst_right_case_ctx_lookups n a p t u v g xp ls rs k xl (m : WfWorldT) σ :
  m ⊨ ctx_denote_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl) ->
  (m : WorldT) σ ->
  σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\
  σ !! xp = Some (vnat p) /\ σ !! rs = Some (vnat (n-p)) /\
  σ !! k = Some (vnat (a+p)) /\ σ !! xl = Some (vconst (ctree t)).
Proof.
  intros Hctx Hσ.
  destruct (bst_right_case_ctx_denote_inv n a p t u v g xp ls rs k xl m Hctx)
    as [Hbase [Hxp [Hrs [Hk Hxl]]]].
  destruct (bst_call_ctx_lookup n a u v g m σ Hbase Hσ) as [Hu Hv].
  split; [exact Hu|]. split; [exact Hv|]. repeat split;
    eapply const_precise_bind_lookup; eassumption.
Qed.

Lemma bst_right_case_ctx_fixed n a p t u v g xp ls rs k xl (m : WfWorldT) σ τ :
  m ⊨ ctx_denote_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl) ->
  (m : WorldT) σ -> (m : WorldT) τ ->
  store_restrict σ {[u;v;xp;rs;k;xl]} = store_restrict τ {[u;v;xp;rs;k;xl]}.
Proof.
  intros Hctx Hσ Hτ.
  destruct (bst_right_case_ctx_lookups n a p t u v g xp ls rs k xl m σ Hctx Hσ)
    as [Hσu [Hσv [Hσp [Hσr [Hσk Hσl]]]]].
  destruct (bst_right_case_ctx_lookups n a p t u v g xp ls rs k xl m τ Hctx Hτ)
    as [Hτu [Hτv [Hτp [Hτr [Hτk Hτl]]]]].
  apply store_restrict_eq_on. intros z Hz.
  assert (Hz' : z=u \/ z=v \/ z=xp \/ z=rs \/ z=k \/ z=xl) by (clear -Hz; set_solver).
  destruct Hz' as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    first [exact (eq_trans Hσu (eq_sym Hτu))|exact (eq_trans Hσv (eq_sym Hτv))|
           exact (eq_trans Hσp (eq_sym Hτp))|exact (eq_trans Hσr (eq_sym Hτr))|
           exact (eq_trans Hσk (eq_sym Hτk))|exact (eq_trans Hσl (eq_sym Hτl))].
Qed.

Lemma bst_right_case_erasure_lookups n a p t u v g xp ls rs k xl :
  u <> v -> u <> g -> v <> g ->
  wf_ctx_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl) ->
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! u = Some (TBase TNat) /\
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! v = Some (TBase TNat) /\
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! g = Some BSTProgram.range_basic_ty /\
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! xp = Some (TBase TNat) /\
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! ls = Some (TBase TNat) /\
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! rs = Some (TBase TNat) /\
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! k = Some (TBase TNat) /\
  erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! xl = Some (TBase TTree).
Proof.
  intros Huv Hug Hvg Hwf.
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  unfold bst_right_case_ctx,bst_right_case_prefix_ctx in Hwf |- *.
  pose proof (proj1 Hwf) as Hw4.
  pose proof (proj1 Hw4) as Hw3.
  pose proof (proj1 Hw3) as Hw2.
  pose proof (proj1 Hw2) as Hw1.
  repeat split.
  - do 5 apply erase_ctx_comma_lookup_old. exact Hu.
  - do 5 apply erase_ctx_comma_lookup_old. exact Hv.
  - do 5 apply erase_ctx_comma_lookup_old. exact Hg.
  - do 4 apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g) xp (nat_singleton_ty p) Hw1).
  - do 3 apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅ (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p))) ls nat_over_ty Hw2).
  - do 2 apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅ (CtxComma (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p))) (CtxBind ls nat_over_ty)) rs (nat_singleton_ty (n-p)) Hw3).
  - do 1 apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅ (CtxComma (CtxComma (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p))) (CtxBind ls nat_over_ty)) (CtxBind rs (nat_singleton_ty (n-p)))) k (nat_singleton_ty (a+p)) Hw4).
  - exact (erase_ctx_comma_lookup_new_wf ∅ (CtxComma (CtxComma (CtxComma (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p))) (CtxBind ls nat_over_ty)) (CtxBind rs (nat_singleton_ty (n-p)))) (CtxBind k (nat_singleton_ty (a+p)))) xl (const_precise_ty (ctree t)) Hwf).
Qed.

Lemma bst_right_case_recursive_typed Φ n a p t u v g xp ls rs k xl :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  k ∉ ({[u;v;g;xp;ls;rs]} : aset) -> xl ∉ ({[u;v;g;xp;ls;rs;k]} : aset) ->
  1 <= p <= n ->
  has_context_type Φ ∅ (bst_call_ctx (n-p) (a+p) rs k g)
    (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar rs) (vfvar k) (vbvar 0))) ->
  has_context_type Φ ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl)
    (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g))
    (CTUnder TTree (bst_right_qual {[u;v]} xp xl n a)).
Proof.
  intros Huv Hug Hvg Hxp Hls Hrs Hk Hxl Hp HIH.
  set (Γ := bst_right_case_ctx n a p t u v g xp ls rs k xl).
  assert (HΓ : wf_ctx_under ∅ Γ) by (apply bst_right_case_ctx_wf; assumption).
  destruct (bst_right_case_erasure_lookups n a p t u v g xp ls rs k xl Huv Hug Hvg HΓ)
    as [Hu [Hv [Hg [HxpT [_ [HrsT [HkT HxlT]]]]]]].
  assert (HF : ({[u;v]} ∪ {[xp;xl;rs;k]}) ⊆ dom (erase_ctx Γ)).
  { assert (Du : u ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Dv : v ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Dp : xp ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Dr : rs ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Dk : k ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Dl : xl ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    clear -Du Dv Dp Dr Dk Dl. set_solver. }
  eapply CT_Sub.
  - split; [exact HΓ|]. split.
    + unfold bst_right_qual. apply param_result_qual_wf. clear -HF. set_solver.
    + apply bst_call_variables_basic_typed; assumption.
  - eapply CT_CtxSub; [|exact HIH|].
    + split; [exact HΓ|]. split.
      * apply q_bst_free_wf; clear -HF; set_solver.
      * apply bst_call_variables_basic_typed; assumption.
    + assert (Hrk : rs <> k) by (clear -Hk; set_solver).
      assert (Hrg : rs <> g) by (clear -Hrs; set_solver).
      assert (Hkg : k <> g) by (clear -Hk; set_solver).
      destruct (bst_call_ctx_lookups (n-p) (a+p) rs k g Hrk Hrg Hkg)
        as [Hrs0 [Hk0 Hg0]].
      pose proof (typing_wf_under _ _ _ _ _ HIH) as Hwf0.
      assert (HX : fv_tm (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g)) ∪
        fv_cty (CTUnder TTree (q_tree_bst_range (vfvar rs) (vfvar k) (vbvar 0))) ⊆ {[rs;k;g]}).
      { rewrite bst_call_variables_fv,fv_under_qual,q_bst_free_dom.
        change (({[rs;k;g]} : gset atom) ∪ {[rs;k]} ⊆ {[rs;k;g]}). set_solver. }
      split; [exact HΓ|]. split; [exact (proj1 Hwf0)|]. split.
      * intros z Hz. assert (Hz' : z=rs \/ z=k \/ z=g) by (clear -HX Hz; set_solver).
        destruct Hz' as [-> | [-> | ->]].
        all: first [exact (eq_trans HrsT (eq_sym Hrs0))|
                    exact (eq_trans HkT (eq_sym Hk0))|exact (eq_trans Hg (eq_sym Hg0))].
      * intros m Hctx. exists m. split; [apply res_restrict_le|].
        destruct (bst_right_case_ctx_denote_inv n a p t u v g xp ls rs k xl m Hctx)
          as [Hbase [_ [Hrsbind [Hkbind _]]]].
        destruct (bst_call_ctx_denote_inv n a u v g m Hbase) as [_ [_ Hgbind]].
        apply bst_call_ctx_denote_intro; assumption.
  - eapply bst_right_fixed_call_subtype with (p:=p); [exact HΓ|exact HF|exact Hp| |].
    + intros m Hctx σ τ Hσ Hτ.
      replace ({[u;v]} ∪ {[xp;xl;rs;k]} : aset) with ({[u;v;xp;rs;k;xl]} : aset)
        by (clear; set_solver).
      exact (bst_right_case_ctx_fixed n a p t u v g xp ls rs k xl m σ τ Hctx Hσ Hτ).
    + intros m σ Hctx Hσ.
      destruct (bst_right_case_ctx_lookups n a p t u v g xp ls rs k xl m σ Hctx Hσ)
        as [_ [_ [Hp' [Hrs' [Hk' _]]]]]. auto.
Qed.

Lemma bst_right_case_fiber_model Γ n a p t u v g xp ls rs k xl (m mfib : WfWorldT) σ s :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ Γ ->
  wf_ctx_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl) ->
  erase_ctx Γ = erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) ->
  m ⊨ ctx_denote_under ∅ Γ -> m ⊨ ctx_denote_under ∅ (CtxBind g range_ty) ->
  res_fiber_from_projection m {[u;v;xp;rs;k;xl]} σ mfib -> (mfib : WorldT) s ->
  s !! u = Some (vnat n) -> s !! v = Some (vnat a) ->
  s !! xp = Some (vnat p) -> s !! rs = Some (vnat (n-p)) ->
  s !! k = Some (vnat (a+p)) -> s !! xl = Some (vconst (ctree t)) ->
  mfib ⊨ ctx_denote_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl).
Proof.
  intros Huv Hug Hvg HΓ Hcase Herase Hctx Hrange Hfib Hs Hu Hv Hp Hrs Hk Hxl.
  destruct (bst_right_case_erasure_lookups n a p t u v g xp ls rs k xl Huv Hug Hvg Hcase)
    as [Hut [Hvt [_ [Hpt [Hlst [Hrst [Hkt Hlt]]]]]]].
  assert (Hlookup : forall x T,
    erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! x = Some T ->
    erase_ctx Γ !! x = Some T).
  { intros x T Hx. exact (eq_trans (f_equal (fun Δ : gmap atom ty => Δ !! x) Herase) Hx). }
  assert (Hconst : forall x c, x ∈ ({[u;v;xp;rs;k;xl]} : aset) ->
    erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl) !! x = Some (TBase (base_ty_of_const c)) ->
    s !! x = Some (vconst c) ->
    mfib ⊨ ctx_denote_under ∅ (CtxBind x (const_precise_ty c))).
  { intros x c HX Hxt Hsx.
    eapply (ctx_const_bind_denote_fiber ∅ Γ x c m mfib {[u;v;xp;rs;k;xl]} σ s);
      [exact HΓ|exact (Hlookup _ _ Hxt)|exact Hctx|exact HX|exact Hfib|exact Hs|exact Hsx]. }
  assert (Hub : mfib ⊨ ctx_denote_under ∅ (CtxBind u (nat_singleton_ty n))).
  { apply (Hconst u (cnat n)); [change (u ∈ ({[u;v;xp;rs;k;xl]} : gset atom)); set_solver|exact Hut|exact Hu]. }
  assert (Hvb : mfib ⊨ ctx_denote_under ∅ (CtxBind v (nat_singleton_ty a))).
  { apply (Hconst v (cnat a)); [change (v ∈ ({[u;v;xp;rs;k;xl]} : gset atom)); set_solver|exact Hvt|exact Hv]. }
  assert (Hpb : mfib ⊨ ctx_denote_under ∅ (CtxBind xp (nat_singleton_ty p))).
  { apply (Hconst xp (cnat p)); [change (xp ∈ ({[u;v;xp;rs;k;xl]} : gset atom)); set_solver|exact Hpt|exact Hp]. }
  assert (Hrb : mfib ⊨ ctx_denote_under ∅ (CtxBind rs (nat_singleton_ty (n-p)))).
  { apply (Hconst rs (cnat (n-p))); [change (rs ∈ ({[u;v;xp;rs;k;xl]} : gset atom)); set_solver|exact Hrst|exact Hrs]. }
  assert (Hkb : mfib ⊨ ctx_denote_under ∅ (CtxBind k (nat_singleton_ty (a+p)))).
  { apply (Hconst k (cnat (a+p))); [change (k ∈ ({[u;v;xp;rs;k;xl]} : gset atom)); set_solver|exact Hkt|exact Hk]. }
  assert (Hlb : mfib ⊨ ctx_denote_under ∅ (CtxBind xl (const_precise_ty (ctree t)))).
  { apply (Hconst xl (ctree t)); [change (xl ∈ ({[u;v;xp;rs;k;xl]} : gset atom)); set_solver|exact Hlt|exact Hxl]. }
  apply bst_right_case_ctx_denote_intro;
    [exact Hcase| |exact Hpb| |exact Hrb|exact Hkb|exact Hlb].
  - apply bst_call_ctx_denote_intro; [exact Huv|exact Hub|exact Hvb|].
    eapply bst_range_binding_fiber; [exact Hrange|exact Hfib].
  - apply over_top_bind_denote_from_basic_world.
    eapply basic_world_formula_res_subset.
    + eapply res_subset_fiber_source; exact Hfib.
    + exact (ctx_denote_under_basic_singleton ∅ Γ ls _ m HΓ (Hlookup _ _ Hlst) Hctx).
Qed.

Lemma bst_right_case_fiber_cover Γ n a u v g xp ls rs k xl :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ Γ ->
  (forall p t, wf_ctx_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl)) ->
  (forall p t, erase_ctx Γ = erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl)) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ -> m ⊨ ctx_denote_under ∅ (CtxBind g range_ty)) ->
  (forall m s, m ⊨ ctx_denote_under ∅ Γ -> (m : WorldT) s ->
    s !! u = Some (vnat n) /\ s !! v = Some (vnat a) /\
    exists p t, 1 <= p <= n /\ s !! xp = Some (vnat p) /\
      s !! rs = Some (vnat (n-p)) /\ s !! k = Some (vnat (a+p)) /\
      s !! xl = Some (vconst (ctree t))) ->
  forall m, m ⊨ ctx_denote_under ∅ Γ -> forall σ mfib,
    res_fiber_from_projection m {[u;v;xp;rs;k;xl]} σ mfib ->
    exists p t, 1 <= p <= n /\
      mfib ⊨ ctx_denote_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl).
Proof.
  intros Huv Hug Hvg HΓ Hcase Herase Hrange Hnums m Hctx σ mfib Hfib.
  destruct (world_wf mfib) as [[s Hs] _].
  pose proof (res_fiber_from_projection_store_source m mfib _ σ s Hfib Hs) as Hsm.
  destruct (Hnums m s Hctx Hsm) as [Hu [Hv [p [t [Hp [Hxp [Hrs [Hk Hxl]]]]]]]].
  exists p,t. split; [exact Hp|]. eapply bst_right_case_fiber_model; eauto.
Qed.

Lemma bst_right_recursive_context_typed Φ Γ n a u v g xp ls rs k xl :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  ls ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;ls]} : aset) ->
  k ∉ ({[u;v;g;xp;ls;rs]} : aset) -> xl ∉ ({[u;v;g;xp;ls;rs;k]} : aset) ->
  context_typing_wf ∅ Γ
    (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g))
    (CTUnder TTree (bst_right_qual {[u;v]} xp xl n a)) ->
  (forall p t, erase_ctx Γ = erase_ctx (bst_right_case_ctx n a p t u v g xp ls rs k xl)) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ -> m ⊨ ctx_denote_under ∅ (CtxBind g range_ty)) ->
  (forall m s, m ⊨ ctx_denote_under ∅ Γ -> (m : WorldT) s ->
    s !! u = Some (vnat n) /\ s !! v = Some (vnat a) /\
    exists p t, 1 <= p <= n /\ s !! xp = Some (vnat p) /\
      s !! rs = Some (vnat (n-p)) /\ s !! k = Some (vnat (a+p)) /\
      s !! xl = Some (vconst (ctree t))) ->
  (forall p, 1 <= p <= n -> n-p<n ->
    has_context_type Φ ∅ (bst_call_ctx (n-p) (a+p) rs k g)
      (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g))
      (CTUnder TTree (q_tree_bst_range (vfvar rs) (vfvar k) (vbvar 0)))) ->
  has_context_type Φ ∅ Γ
    (NatArithmetic.app3 bst_gen_value (vfvar rs) (vfvar k) (vfvar g))
    (CTUnder TTree (bst_right_qual {[u;v]} xp xl n a)).
Proof.
  intros Huv Hug Hvg Hxp Hls Hrs Hk Hxl Hwf Herase Hrange Hnums HIH.
  assert (Hcases : forall p t, wf_ctx_under ∅ (bst_right_case_ctx n a p t u v g xp ls rs k xl))
    by (intros p t; apply bst_right_case_ctx_wf; assumption).
  eapply CT_FiberCases with (I:=(sig (fun p : nat => 1 <= p <= n) * tree)%type)
    (X:={[u;v;xp;rs;k;xl]})
    (cases:=fun c => bst_right_case_ctx n a (proj1_sig (fst c)) (snd c) u v g xp ls rs k xl).
  - exact Hwf.
  - intros [[p Hp] t]. symmetry. apply Herase.
  - intros [[p Hp] t]. cbn [fst snd proj1_sig]. apply bst_right_case_recursive_typed;
      try assumption. apply HIH; [exact Hp|lia].
  - apply context_under_fiberwise_joinable; [exact Hwf|].
    rewrite bst_call_variables_fv,fv_under_qual.
    unfold bst_right_qual. rewrite param_result_qual_dom.
    change (({[u;v;xp;rs;k;xl]} : gset atom) ⊆ {[rs;k;g]} ∪ ({[u;v]} ∪ {[xp;xl]})).
    set_solver.
  - intros m Hctx σ mfib Hfib.
    destruct (bst_right_case_fiber_cover Γ n a u v g xp ls rs k xl
      Huv Hug Hvg (proj1 Hwf) Hcases Herase Hrange Hnums m Hctx σ mfib Hfib)
      as [p [t [Hp Hmodel]]].
    exists (exist _ p Hp,t). exact Hmodel.
Qed.
