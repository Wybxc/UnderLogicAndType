(** Concrete contexts for the left recursive-call fibers.  The case only
    fixes relevant data; the persistent range value remains arbitrary. *)
From CaseStudy Require Import BSTContext BSTSupport BSTNodeTypes BSTRecursiveSupport
  BSTGeneratorProgram BSTGeneratorUnfolding NatArithmetic.
From Denotation Require Import Context ResultQualifier QualifierStore.
From ContextTyping Require Import Typing TypingRegular BasicBindings ConstCases
  NatCases Subtyping FiberSupport.

Definition bst_left_case_ctx n a p u v g xp sz rs k : ctx :=
  CtxComma
    (CtxComma
      (CtxComma
        (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p)))
        (CtxBind sz (nat_singleton_ty (p-1))))
      (CtxBind rs nat_over_ty))
    (CtxBind k nat_over_ty).

Lemma bst_left_case_ctx_wf n a p u v g xp sz rs k :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  sz ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;sz]} : aset) ->
  k ∉ ({[u;v;g;xp;sz;rs]} : aset) ->
  wf_ctx_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k).
Proof.
  intros Huv Hug Hvg Hxp Hsz Hrs Hk. unfold bst_left_case_ctx.
  do 4 (apply wf_ctx_comma_closed_bind;
    [|cbn [ctx_dom bst_call_ctx nat_pair_ctx]; set_solver|
     first [apply nat_over_wf|apply nat_singleton_wf]]).
  apply bst_call_ctx_wf; assumption.
Qed.

Lemma bst_left_case_ctx_denote_intro n a p u v g xp sz rs k (m : WfWorldT) :
  wf_ctx_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k) ->
  m ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g) ->
  m ⊨ ctx_denote_under ∅ (CtxBind xp (nat_singleton_ty p)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind sz (nat_singleton_ty (p-1))) ->
  m ⊨ ctx_denote_under ∅ (CtxBind rs nat_over_ty) ->
  m ⊨ ctx_denote_under ∅ (CtxBind k nat_over_ty) ->
  m ⊨ ctx_denote_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k).
Proof.
  intros Hwf Hbase Hxp Hsz Hrs Hk. unfold bst_left_case_ctx in Hwf |- *.
  pose proof (proj1 Hwf) as Hw3.
  pose proof (proj1 Hw3) as Hw2.
  pose proof (proj1 Hw2) as Hw1.
  apply ctx_denote_under_comma_intro; [exact Hw3| |].
  2: { rewrite ctx_denote_closed_env; [exact Hk|apply nat_over_fv]. }
  apply ctx_denote_under_comma_intro; [exact Hw2| |].
  2: { rewrite ctx_denote_closed_env; [exact Hrs|apply nat_over_fv]. }
  apply ctx_denote_under_comma_intro; [exact Hw1| |].
  2: { rewrite ctx_denote_closed_env; [exact Hsz|apply nat_singleton_fv]. }
  apply ctx_denote_under_comma_intro; [exact (proj1 Hw1)|exact Hbase|].
  rewrite ctx_denote_closed_env; [exact Hxp|apply nat_singleton_fv].
Qed.

Lemma bst_left_case_ctx_denote_inv n a p u v g xp sz rs k (m : WfWorldT) :
  m ⊨ ctx_denote_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k) ->
  m ⊨ ctx_denote_under ∅ (bst_call_ctx n a u v g) /\
  m ⊨ ctx_denote_under ∅ (CtxBind xp (nat_singleton_ty p)) /\
  m ⊨ ctx_denote_under ∅ (CtxBind sz (nat_singleton_ty (p-1))).
Proof.
  intros Hctx. unfold bst_left_case_ctx in Hctx.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hctx) as Hrs.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hrs) as Hsz.
  pose proof (ctx_denote_under_comma_left ∅ _ _ m Hsz) as Hxp.
  split; [exact (ctx_denote_under_comma_left ∅ _ _ m Hxp)|]. split.
  - eapply ctx_denote_comma_closed_right; [apply nat_singleton_fv|exact Hxp].
  - eapply ctx_denote_comma_closed_right; [apply nat_singleton_fv|exact Hsz].
Qed.

Lemma bst_left_case_ctx_lookups n a p u v g xp sz rs k (m : WfWorldT) σ :
  m ⊨ ctx_denote_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k) ->
  (m : WorldT) σ ->
  σ !! u = Some (vnat n) /\ σ !! v = Some (vnat a) /\
  σ !! xp = Some (vnat p) /\ σ !! sz = Some (vnat (p-1)).
Proof.
  intros Hctx Hσ.
  destruct (bst_left_case_ctx_denote_inv n a p u v g xp sz rs k m Hctx)
    as [Hbase [Hxp Hsz]].
  destruct (bst_call_ctx_lookup n a u v g m σ Hbase Hσ) as [Hu Hv].
  split; [exact Hu|]. split; [exact Hv|]. split;
    eapply const_precise_bind_lookup; eassumption.
Qed.

Lemma bst_left_case_ctx_fixed n a p u v g xp sz rs k (m : WfWorldT) σ τ :
  m ⊨ ctx_denote_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k) ->
  (m : WorldT) σ -> (m : WorldT) τ ->
  store_restrict σ {[u;v;xp;sz]} = store_restrict τ {[u;v;xp;sz]}.
Proof.
  intros Hctx Hσ Hτ.
  destruct (bst_left_case_ctx_lookups n a p u v g xp sz rs k m σ Hctx Hσ)
    as [Hσu [Hσv [Hσp Hσs]]].
  destruct (bst_left_case_ctx_lookups n a p u v g xp sz rs k m τ Hctx Hτ)
    as [Hτu [Hτv [Hτp Hτs]]].
  apply store_restrict_eq_on. intros z Hz.
  assert (Hz' : z=u \/ z=v \/ z=xp \/ z=sz) by (clear -Hz; set_solver).
  destruct Hz' as [-> | [-> | [-> | ->]]];
    first [exact (eq_trans Hσu (eq_sym Hτu))|exact (eq_trans Hσv (eq_sym Hτv))|
           exact (eq_trans Hσp (eq_sym Hτp))|exact (eq_trans Hσs (eq_sym Hτs))].
Qed.

Lemma bst_left_case_erasure_lookups n a p u v g xp sz rs k :
  u <> v -> u <> g -> v <> g ->
  wf_ctx_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k) ->
  erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! u = Some (TBase TNat) /\
  erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! v = Some (TBase TNat) /\
  erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! g = Some BSTProgram.range_basic_ty /\
  erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! xp = Some (TBase TNat) /\
  erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! sz = Some (TBase TNat) /\
  erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! rs = Some (TBase TNat) /\
  erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! k = Some (TBase TNat).
Proof.
  intros Huv Hug Hvg Hwf.
  destruct (bst_call_ctx_lookups n a u v g Huv Hug Hvg) as [Hu [Hv Hg]].
  unfold bst_left_case_ctx in Hwf |- *.
  pose proof (proj1 Hwf) as Hwf3.
  pose proof (proj1 Hwf3) as Hwf2.
  pose proof (proj1 Hwf2) as Hwf1.
  repeat split.
  - do 4 apply erase_ctx_comma_lookup_old. exact Hu.
  - do 4 apply erase_ctx_comma_lookup_old. exact Hv.
  - do 4 apply erase_ctx_comma_lookup_old. exact Hg.
  - do 3 apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅ (bst_call_ctx n a u v g)
      xp (nat_singleton_ty p) Hwf1).
  - do 2 apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅
      (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p)))
      sz (nat_singleton_ty (p-1)) Hwf2).
  - apply erase_ctx_comma_lookup_old.
    exact (erase_ctx_comma_lookup_new_wf ∅
      (CtxComma
        (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p)))
        (CtxBind sz (nat_singleton_ty (p-1)))) rs nat_over_ty Hwf3).
  - exact (erase_ctx_comma_lookup_new_wf ∅
      (CtxComma
        (CtxComma
          (CtxComma (bst_call_ctx n a u v g) (CtxBind xp (nat_singleton_ty p)))
          (CtxBind sz (nat_singleton_ty (p-1))))
        (CtxBind rs nat_over_ty)) k nat_over_ty Hwf).
Qed.

Lemma bst_left_case_recursive_typed Φ n a p u v g xp sz rs k :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  sz ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;sz]} : aset) ->
  k ∉ ({[u;v;g;xp;sz;rs]} : aset) -> 1 <= p <= n ->
  has_context_type Φ ∅ (bst_call_ctx (p-1) a sz v g)
    (NatArithmetic.app3 bst_gen_value (vfvar sz) (vfvar v) (vfvar g))
    (CTUnder TTree (q_tree_bst_range (vfvar sz) (vfvar v) (vbvar 0))) ->
  has_context_type Φ ∅ (bst_left_case_ctx n a p u v g xp sz rs k)
    (NatArithmetic.app3 bst_gen_value (vfvar sz) (vfvar v) (vfvar g))
    (CTUnder TTree (bst_left_qual {[u;v]} xp n a)).
Proof.
  intros Huv Hug Hvg Hxp Hsz Hrs Hk Hp HIH.
  set (Γ := bst_left_case_ctx n a p u v g xp sz rs k).
  assert (HΓ : wf_ctx_under ∅ Γ) by (apply bst_left_case_ctx_wf; assumption).
  destruct (bst_left_case_erasure_lookups n a p u v g xp sz rs k Huv Hug Hvg HΓ)
    as [Hu [Hv [Hg [HxpT [HszT _]]]]].
  assert (HF : ({[u;v]} ∪ {[xp;sz;v]}) ⊆ dom (erase_ctx Γ)).
  { assert (Du : u ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Dv : v ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Dp : xp ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    assert (Ds : sz ∈ dom (erase_ctx Γ)) by (apply elem_of_dom; eauto).
    clear -Du Dv Dp Ds. set_solver. }
  eapply CT_Sub.
  - split; [exact HΓ|]. split.
    + unfold bst_left_qual. apply param_result_qual_wf. clear -HF. set_solver.
    + apply bst_call_variables_basic_typed; assumption.
  - eapply CT_CtxSub; [|exact HIH|].
    + split; [exact HΓ|]. split.
      * apply q_bst_free_wf; clear -HF; set_solver.
      * apply bst_call_variables_basic_typed; assumption.
    + assert (Hsv : sz <> v) by (clear -Hsz; set_solver).
      assert (Hsg : sz <> g) by (clear -Hsz; set_solver).
      destruct (bst_call_ctx_lookups (p-1) a sz v g Hsv Hsg Hvg)
        as [Hsz0 [Hv0 Hg0]].
      pose proof (typing_wf_under _ _ _ _ _ HIH) as Hwf0.
      pose proof (context_typing_wf_fv_tm_subset _ _ _ _ Hwf0) as HeFV.
      pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf0) as HτFV.
      assert (HX : fv_tm (NatArithmetic.app3 bst_gen_value (vfvar sz) (vfvar v) (vfvar g)) ∪
        fv_cty (CTUnder TTree (q_tree_bst_range (vfvar sz) (vfvar v) (vbvar 0))) ⊆ {[sz;v;g]}).
      { rewrite bst_call_ctx_erasure in HeFV,HτFV.
        repeat setoid_rewrite (dom_union_L (M:=gmap atom) (D:=aset)) in HeFV.
        repeat setoid_rewrite (dom_union_L (M:=gmap atom) (D:=aset)) in HτFV.
        repeat setoid_rewrite (dom_singleton_L (M:=gmap atom) (D:=aset)) in HeFV.
        repeat setoid_rewrite (dom_singleton_L (M:=gmap atom) (D:=aset)) in HτFV.
        clear -HeFV HτFV. set_solver. }
      split; [exact HΓ|]. split; [exact (proj1 Hwf0)|]. split.
      * intros z Hz. assert (Hz' : z=sz \/ z=v \/ z=g) by (clear -HX Hz; set_solver).
        destruct Hz' as [-> | [-> | ->]].
        all: first [exact (eq_trans HszT (eq_sym Hsz0))|
                    exact (eq_trans Hv (eq_sym Hv0))|exact (eq_trans Hg (eq_sym Hg0))].
      * intros m Hctx. exists m. split; [apply res_restrict_le|].
        destruct (bst_left_case_ctx_denote_inv n a p u v g xp sz rs k m Hctx)
          as [Hbase [_ Hszbind]].
        destruct (bst_call_ctx_denote_inv n a u v g m Hbase) as [_ [Hvbind Hgbind]].
        apply bst_call_ctx_denote_intro; assumption.
  - eapply bst_left_fixed_call_subtype with (p:=p); [exact HΓ|exact HF|exact Hp| |].
    + intros m Hctx σ τ Hσ Hτ.
      replace ({[u;v]} ∪ {[xp;sz;v]} : aset) with ({[u;v;xp;sz]} : aset)
        by (clear; set_solver).
      exact (bst_left_case_ctx_fixed n a p u v g xp sz rs k m σ τ Hctx Hσ Hτ).
    + intros m σ Hctx Hσ.
      destruct (bst_left_case_ctx_lookups n a p u v g xp sz rs k m σ Hctx Hσ)
        as [_ [Hv' [Hp' Hsz']]]. auto.
Qed.

Lemma bst_left_case_fiber_model Γ n a p u v g xp sz rs k (m mfib : WfWorldT) σ s :
  u <> v -> u <> g -> v <> g ->
  wf_ctx_under ∅ Γ ->
  wf_ctx_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k) ->
  erase_ctx Γ = erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) ->
  m ⊨ ctx_denote_under ∅ Γ ->
  m ⊨ ctx_denote_under ∅ (CtxBind g range_ty) ->
  res_fiber_from_projection m {[u;v;xp;sz]} σ mfib -> (mfib : WorldT) s ->
  s !! u = Some (vnat n) -> s !! v = Some (vnat a) ->
  s !! xp = Some (vnat p) -> s !! sz = Some (vnat (p-1)) ->
  mfib ⊨ ctx_denote_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k).
Proof.
  intros Huv Hug Hvg HΓ Hcase Herase Hctx Hrange Hfib Hs Hu Hv Hp Hsz.
  destruct (bst_left_case_erasure_lookups n a p u v g xp sz rs k Huv Hug Hvg Hcase)
    as [Hut [Hvt [_ [Hpt [Hst [Hrst Hkt]]]]]].
  assert (Hlookup : forall x T,
    erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k) !! x = Some T ->
    erase_ctx Γ !! x = Some T).
  { intros x T Hx. exact (eq_trans (f_equal (fun Δ : gmap atom ty => Δ !! x) Herase) Hx). }
  assert (Hub : mfib ⊨ ctx_denote_under ∅ (CtxBind u (nat_singleton_ty n))).
  { eapply const_bind_denote_fiber with (x:=u) (c:=cnat n)
      (m:=m) (X:={[u;v;xp;sz]}) (σ:=σ) (s:=s).
    - change (u ∈ ({[u;v;xp;sz]} : gset atom)). set_solver.
    - exact (ctx_denote_under_basic_singleton ∅ Γ u _ m HΓ (Hlookup _ _ Hut) Hctx).
    - exact Hfib.
    - exact Hs.
    - exact Hu. }
  assert (Hvb : mfib ⊨ ctx_denote_under ∅ (CtxBind v (nat_singleton_ty a))).
  { eapply const_bind_denote_fiber with (x:=v) (c:=cnat a)
      (m:=m) (X:={[u;v;xp;sz]}) (σ:=σ) (s:=s).
    - change (v ∈ ({[u;v;xp;sz]} : gset atom)). set_solver.
    - exact (ctx_denote_under_basic_singleton ∅ Γ v _ m HΓ (Hlookup _ _ Hvt) Hctx).
    - exact Hfib.
    - exact Hs.
    - exact Hv. }
  assert (Hpb : mfib ⊨ ctx_denote_under ∅ (CtxBind xp (nat_singleton_ty p))).
  { eapply const_bind_denote_fiber with (x:=xp) (c:=cnat p)
      (m:=m) (X:={[u;v;xp;sz]}) (σ:=σ) (s:=s).
    - change (xp ∈ ({[u;v;xp;sz]} : gset atom)). set_solver.
    - exact (ctx_denote_under_basic_singleton ∅ Γ xp _ m HΓ (Hlookup _ _ Hpt) Hctx).
    - exact Hfib.
    - exact Hs.
    - exact Hp. }
  assert (Hsb : mfib ⊨ ctx_denote_under ∅ (CtxBind sz (nat_singleton_ty (p-1)))).
  { eapply const_bind_denote_fiber with (x:=sz) (c:=cnat (p-1))
      (m:=m) (X:={[u;v;xp;sz]}) (σ:=σ) (s:=s).
    - change (sz ∈ ({[u;v;xp;sz]} : gset atom)). set_solver.
    - exact (ctx_denote_under_basic_singleton ∅ Γ sz _ m HΓ (Hlookup _ _ Hst) Hctx).
    - exact Hfib.
    - exact Hs.
    - exact Hsz. }
  apply bst_left_case_ctx_denote_intro; [exact Hcase| |exact Hpb|exact Hsb| |].
  - apply bst_call_ctx_denote_intro; [exact Huv|exact Hub|exact Hvb|].
    eapply bst_range_binding_fiber; [exact Hrange|exact Hfib].
  - apply over_top_bind_denote_from_basic_world.
    eapply basic_world_formula_res_subset.
    + eapply res_subset_fiber_source; exact Hfib.
    + exact (ctx_denote_under_basic_singleton ∅ Γ rs _ m HΓ (Hlookup _ _ Hrst) Hctx).
  - apply over_top_bind_denote_from_basic_world.
    eapply basic_world_formula_res_subset.
    + eapply res_subset_fiber_source; exact Hfib.
    + exact (ctx_denote_under_basic_singleton ∅ Γ k _ m HΓ (Hlookup _ _ Hkt) Hctx).
Qed.

Lemma bst_left_case_fiber_cover Γ n a u v g xp sz rs k :
  u <> v -> u <> g -> v <> g -> wf_ctx_under ∅ Γ ->
  (forall p, wf_ctx_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k)) ->
  (forall p, erase_ctx Γ = erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k)) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ ->
    m ⊨ ctx_denote_under ∅ (CtxBind g range_ty)) ->
  (forall m s, m ⊨ ctx_denote_under ∅ Γ -> (m : WorldT) s ->
    s !! u = Some (vnat n) /\ s !! v = Some (vnat a) /\
    exists p, 1 <= p <= n /\ s !! xp = Some (vnat p) /\ s !! sz = Some (vnat (p-1))) ->
  forall m, m ⊨ ctx_denote_under ∅ Γ -> forall σ mfib,
    res_fiber_from_projection m {[u;v;xp;sz]} σ mfib ->
    exists p, 1 <= p <= n /\
      mfib ⊨ ctx_denote_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k).
Proof.
  intros Huv Hug Hvg HΓ Hcase Herase Hrange Hnums m Hctx σ mfib Hfib.
  destruct (world_wf mfib) as [[s Hs] _].
  pose proof (res_fiber_from_projection_store_source m mfib _ σ s Hfib Hs) as Hsm.
  destruct (Hnums m s Hctx Hsm) as [Hu [Hv [p [Hp [Hxp Hsz]]]]].
  exists p. split; [exact Hp|].
  eapply bst_left_case_fiber_model; eauto.
Qed.

(** A genuine syntax derivation for the left call in the unclassified
    continuation.  The remaining premises describe that continuation;
    recursive typing is required only at strictly smaller concrete sizes. *)
Lemma bst_left_recursive_context_typed Φ Γ n a u v g xp sz rs k :
  u <> v -> u <> g -> v <> g -> xp ∉ ({[u;v;g]} : aset) ->
  sz ∉ ({[u;v;g;xp]} : aset) -> rs ∉ ({[u;v;g;xp;sz]} : aset) ->
  k ∉ ({[u;v;g;xp;sz;rs]} : aset) ->
  context_typing_wf ∅ Γ
    (NatArithmetic.app3 bst_gen_value (vfvar sz) (vfvar v) (vfvar g))
    (CTUnder TTree (bst_left_qual {[u;v]} xp n a)) ->
  (forall p, erase_ctx Γ = erase_ctx (bst_left_case_ctx n a p u v g xp sz rs k)) ->
  (forall m, m ⊨ ctx_denote_under ∅ Γ ->
    m ⊨ ctx_denote_under ∅ (CtxBind g range_ty)) ->
  (forall m s, m ⊨ ctx_denote_under ∅ Γ -> (m : WorldT) s ->
    s !! u = Some (vnat n) /\ s !! v = Some (vnat a) /\
    exists p, 1 <= p <= n /\ s !! xp = Some (vnat p) /\ s !! sz = Some (vnat (p-1))) ->
  (forall p, 1 <= p <= n -> p-1<n ->
    has_context_type Φ ∅ (bst_call_ctx (p-1) a sz v g)
      (NatArithmetic.app3 bst_gen_value (vfvar sz) (vfvar v) (vfvar g))
      (CTUnder TTree (q_tree_bst_range (vfvar sz) (vfvar v) (vbvar 0)))) ->
  has_context_type Φ ∅ Γ
    (NatArithmetic.app3 bst_gen_value (vfvar sz) (vfvar v) (vfvar g))
    (CTUnder TTree (bst_left_qual {[u;v]} xp n a)).
Proof.
  intros Huv Hug Hvg Hxp Hsz Hrs Hk Hwf Herase Hrange Hnums HIH.
  assert (Hcases : forall p, wf_ctx_under ∅ (bst_left_case_ctx n a p u v g xp sz rs k))
    by (intros p; apply bst_left_case_ctx_wf; assumption).
  eapply CT_FiberCases with (I:=sig (fun p : nat => 1 <= p <= n))
    (X:={[u;v;xp;sz]})
    (cases:=fun p => bst_left_case_ctx n a (proj1_sig p) u v g xp sz rs k).
  - exact Hwf.
  - intros [p Hp]. symmetry. apply Herase.
  - intros [p Hp]. cbn [proj1_sig]. apply bst_left_case_recursive_typed;
      try assumption. apply HIH; [exact Hp|lia].
  - apply context_under_fiberwise_joinable; [exact Hwf|].
    rewrite bst_call_variables_fv,fv_under_qual.
    unfold bst_left_qual. rewrite param_result_qual_dom.
    change (({[u;v;xp;sz]} : gset atom) ⊆ {[sz;v;g]} ∪ {[u;v;xp]}).
    set_solver.
  - intros m Hctx σ mfib Hfib.
    destruct (bst_left_case_fiber_cover Γ n a u v g xp sz rs k
      Huv Hug Hvg (proj1 Hwf) Hcases Herase Hrange Hnums m Hctx σ mfib Hfib)
      as [p [Hp Hmodel]].
    exists (exist _ p Hp). exact Hmodel.
Qed.
