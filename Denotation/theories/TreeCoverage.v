(** The variable-denotation part of conditional node construction.
    This lemma proves target reachability in each parameter fiber.
    Introducing a full under denotation additionally needs its guard and
    nonempty target fibers; neither obligation is hidden here. *)
From Denotation Require Import Notation TypeDenote TypeEquivCore TypeEquiv
  ConditionalCoverage BaseCoverage.
From ContextBasicDenotation Require Import TreeCoverage.

Lemma node_coverage_from_variable_denotations
    gas Σ (m : WfWorldT) S xp xk xl xr φP φK φL φR
    (P : StoreT -> nat -> Prop)
    (K : StoreT -> nat -> nat -> Prop)
    (L : StoreT -> nat -> tree -> Prop)
    (R : StoreT -> nat -> tree -> tree -> Prop)
    (Q : StoreT -> tree -> Prop) :
  lty_env_closed Σ ->
  xp ∉ S -> xk ∉ S ∪ {[xp]} -> xl ∉ S ∪ {[xp]} -> xr ∉ S ∪ {[xp;xl]} ->
  qual_dom φP = S -> qual_dom φK = S ∪ {[xp]} ->
  qual_dom φL = S ∪ {[xp]} -> qual_dom φR = S ∪ {[xp;xl]} ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTUnder TNat φP) (tret (vfvar xp)) ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTOver TNat φK) (tret (vfvar xk)) ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTUnder TTree φL) (tret (vfvar xl)) ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTUnder TTree φR) (tret (vfvar xr)) ->
  (forall σ p, (m : WorldT) σ -> P (store_restrict σ S) p ->
    qualifier_holds_store (qual_open_atom 0 xp (typed_result_qual TNat φP))
      (<[xp:=vconst (cnat p)]> σ)) ->
  (forall σ p l, (m : WorldT) σ -> σ !! xp = Some (vconst (cnat p)) ->
    L (store_restrict σ S) p l ->
    qualifier_holds_store (qual_open_atom 0 xl (typed_result_qual TTree φL))
      (<[xl:=vconst (ctree l)]> σ)) ->
  (forall σ p l rr, (m : WorldT) σ ->
    σ !! xp = Some (vconst (cnat p)) -> σ !! xl = Some (vconst (ctree l)) ->
    R (store_restrict σ S) p l rr ->
    qualifier_holds_store (qual_open_atom 0 xr (typed_result_qual TTree φR))
      (<[xr:=vconst (ctree rr)]> σ)) ->
  (forall σ p, (m : WorldT) σ -> σ !! xp = Some (vconst (cnat p)) ->
    qualifier_holds_store (qual_open_atom 0 xk (typed_result_qual TNat φK)) σ ->
    exists k, σ !! xk = Some (vconst (cnat k)) /\ K (store_restrict σ S) p k) ->
  (forall s t, Q s t ->
    exists p k l rr, t = tr_node k l rr /\
      P s p /\ L s p l /\ R s p l rr /\ (forall k', K s p k' -> k' = k)) ->
  forall σ t, (m : WorldT) σ -> Q (store_restrict σ S) t ->
    exists σ', (m : WorldT) σ' /\ store_restrict σ' S = store_restrict σ S /\
      tm_eval_in_store σ' (tnode (vfvar xk) (vfvar xl) (vfvar xr))
        (vconst (ctree t)).
Proof.
  intros HΣ Hxp Hxk Hxl Hxr DP DK DL DR HP HK HL HR
    HPq HLq HRq HKq Hdecomp.
  assert (Hxpφ : xp ∉ qual_dom φP) by (rewrite DP; exact Hxp).
  assert (Hxkφ : xk ∉ qual_dom φK) by (rewrite DK; exact Hxk).
  assert (Hxlφ : xl ∉ qual_dom φL) by (rewrite DL; exact Hxl).
  assert (Hxrφ : xr ∉ qual_dom φR) by (rewrite DR; exact Hxr).
  apply (conditional_node_coverage m S xp xk xl xr P K L R Q).
  - rewrite <- DP.
    eapply under_ret_var_conditional_coverage;
      [exact HΣ|exact Hxpφ|exact HP|].
    intros σ v Hσ [p [-> Hp]]. apply HPq; [exact Hσ|].
    rewrite DP in Hp. exact Hp.
  - intros σ p l Hσ Hpl Hl.
    destruct (under_ret_var_covers_value gas Σ TTree φL xl m σ
      (vconst (ctree l)) HΣ Hxlφ HL Hσ (HLq σ p l Hσ Hpl Hl))
      as [σ' [Hσ' [Hsame Hlook]]].
    rewrite DL in Hsame. exists σ'. auto.
  - intros σ p l rr Hσ Hpl Hll Hr.
    destruct (under_ret_var_covers_value gas Σ TTree φR xr m σ
      (vconst (ctree rr)) HΣ Hxrφ HR Hσ (HRq σ p l rr Hσ Hpl Hll Hr))
      as [σ' [Hσ' [Hsame Hlook]]].
    rewrite DR in Hsame. exists σ'. auto.
  - intros σ p Hσ Hpl. apply HKq; [exact Hσ|exact Hpl|].
    exact (over_ret_var_store_holds gas Σ TNat φK xk m HΣ Hxkφ HK σ Hσ).
  - exact Hdecomp.
Qed.

(** Pure qualifier conditions for a syntactic node rule.  No execution
    certificate or world-denotation premise occurs in this record. *)
Record node_under_graph_spec (S : aset) xp xk xl xr φP φK φL φR Θ
    (P : StoreT -> nat -> Prop) (K : StoreT -> nat -> nat -> Prop)
    (L : StoreT -> nat -> tree -> Prop)
    (R : StoreT -> nat -> tree -> tree -> Prop)
    (Q : StoreT -> tree -> Prop) : Prop := {
  node_graph_fresh_p : xp ∉ S;
  node_graph_fresh_k : xk ∉ S ∪ {[xp]};
  node_graph_fresh_l : xl ∉ S ∪ {[xp]};
  node_graph_fresh_r : xr ∉ S ∪ {[xp;xl]};
  node_graph_dom_p : qual_dom φP = S;
  node_graph_dom_k : qual_dom φK = S ∪ {[xp]};
  node_graph_dom_l : qual_dom φL = S ∪ {[xp]};
  node_graph_dom_r : qual_dom φR = S ∪ {[xp;xl]};
  node_graph_dom_result : qual_dom Θ = S;
  node_graph_pivot : forall σ p, S ⊆ dom (σ : StoreT) -> P (store_restrict σ S) p ->
    qualifier_holds_store (qual_open_atom 0 xp (typed_result_qual TNat φP))
      (<[xp:=vconst (cnat p)]> σ);
  node_graph_left : forall σ p l, S ⊆ dom (σ : StoreT) ->
    σ !! xp = Some (vconst (cnat p)) -> L (store_restrict σ S) p l ->
    qualifier_holds_store (qual_open_atom 0 xl (typed_result_qual TTree φL))
      (<[xl:=vconst (ctree l)]> σ);
  node_graph_right : forall σ p l rr, S ⊆ dom (σ : StoreT) ->
    σ !! xp = Some (vconst (cnat p)) -> σ !! xl = Some (vconst (ctree l)) ->
    R (store_restrict σ S) p l rr ->
    qualifier_holds_store (qual_open_atom 0 xr (typed_result_qual TTree φR))
      (<[xr:=vconst (ctree rr)]> σ);
  node_graph_root : forall σ p, S ⊆ dom (σ : StoreT) ->
    σ !! xp = Some (vconst (cnat p)) ->
    qualifier_holds_store (qual_open_atom 0 xk (typed_result_qual TNat φK)) σ ->
    exists k, σ !! xk = Some (vconst (cnat k)) /\ K (store_restrict σ S) p k;
  node_graph_decompose : forall s t, Q s t ->
    exists p k l rr, t = tr_node k l rr /\
      P s p /\ L s p l /\ R s p l rr /\ (forall k', K s p k' -> k' = k);
  node_graph_target : forall y τ, y ∉ S ->
    qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree Θ)) τ ->
    exists t, τ !! y = Some (vconst (ctree t)) /\ Q (store_restrict τ S) t;
  node_graph_inhabited : forall y s, y ∉ S -> dom (s : StoreT) = S ->
    exists τ, qualifier_holds_store (qual_open_atom 0 y (typed_result_qual TTree Θ)) τ /\
      store_restrict τ S = s
}.

Lemma node_under_graph_denotation gas gasout Σ (m : WfWorldT)
    S xp xk xl xr φP φK φL φR Θ P K L R Q :
  lty_env_closed Σ -> lc_context_ty (CTUnder TTree Θ) ->
  node_under_graph_spec S xp xk xl xr φP φK φL φR Θ P K L R Q ->
  m ⊨ ty_static_guard_formula Σ (CTUnder TTree Θ)
    (tnode (vfvar xk) (vfvar xl) (vfvar xr)) ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTUnder TNat φP) (tret (vfvar xp)) ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTOver TNat φK) (tret (vfvar xk)) ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTUnder TTree φL) (tret (vfvar xl)) ->
  m ⊨ ty_denote_gas (Datatypes.S gas) Σ (CTUnder TTree φR) (tret (vfvar xr)) ->
  m ⊨ ty_denote_gas gasout Σ (CTUnder TTree Θ)
    (tnode (vfvar xk) (vfvar xl) (vfvar xr)).
Proof.
  intros HΣ Hlc Hspec Hstatic HP HK HL HR.
  destruct Hspec as [Hxp Hxk Hxl Hxr DP DK DL DR DΘ HPq HLq HRq HKq
    Hdecomp Htarget Hinhabited].
  assert (Htotal : m ⊨ expr_total_formula (tnode (vfvar xk) (vfvar xl) (vfvar xr))).
  { apply expr_total_formula_models_iff. split.
    - unfold formula_scoped_in_world. rewrite formula_fv_expr_total_formula, tm_lvars_fv.
      pose proof (ty_denote_gas_ret_fvar_world_dom _ _ _ _ _ HK) as Hkm.
      pose proof (ty_denote_gas_ret_fvar_world_dom _ _ _ _ _ HL) as Hlm.
      pose proof (ty_denote_gas_ret_fvar_world_dom _ _ _ _ _ HR) as Hrm.
      cbn [fv_tm fv_value]. clear -Hkm Hlm Hrm. set_solver.
    - split; [apply tm_lvars_lc; repeat constructor|].
      intros σ Hσ.
      destruct (ty_denote_ret_fvar_base_const _ _ (CTOver TNat φK) TNat xk m eq_refl HK σ Hσ)
        as [ck [Hk Hck]].
      destruct (ty_denote_ret_fvar_base_const _ _ (CTUnder TTree φL) TTree xl m eq_refl HL σ Hσ)
        as [cl [Hl Hcl]].
      destruct (ty_denote_ret_fvar_base_const _ _ (CTUnder TTree φR) TTree xr m eq_refl HR σ Hσ)
        as [cr [Hr Hcr]].
      destruct ck; cbn in Hck; try discriminate.
      destruct cl; cbn in Hcl; try discriminate.
      destruct cr; cbn in Hcr; try discriminate.
      eapply tm_total_tree_node_vars; eassumption. }
  assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTUnder TTree Θ)
      (tnode (vfvar xk) (vfvar xl) (vfvar xr))).
  { apply ty_denote_gas_zero_of_guard.
    apply ty_guard_relevant_of_static_full_total; assumption. }
  assert (HSm : S ⊆ world_dom (m : WorldT)).
  { rewrite <- DΘ, <- (context_ty_lvars_under_fv TTree Θ).
    exact (ty_denote_gas_type_lvars_world _ _ _ _ _ Hzero). }
  assert (HSσ : forall σ, (m : WorldT) σ -> S ⊆ dom (σ : StoreT)).
  { intros σ Hσ. change (S ⊆ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ). exact HSm. }
  assert (Hcoverage : forall σ t, (m : WorldT) σ -> Q (store_restrict σ S) t ->
      exists σ', (m : WorldT) σ' /\ store_restrict σ' S = store_restrict σ S /\
      tm_eval_in_store σ' (tnode (vfvar xk) (vfvar xl) (vfvar xr)) (vconst (ctree t))).
  { eapply node_coverage_from_variable_denotations;
      [exact HΣ|exact Hxp|exact Hxk|exact Hxl|exact Hxr|
       exact DP|exact DK|exact DL|exact DR|exact HP|exact HK|exact HL|exact HR| | | | |exact Hdecomp].
    - intros σ p Hσ Hp. apply (HPq σ p); [apply HSσ; exact Hσ|exact Hp].
    - intros σ p l Hσ Hpl Hl. apply (HLq σ p l); [apply HSσ; exact Hσ|exact Hpl|exact Hl].
    - intros σ p l rr Hσ Hpl Hll Hr. apply (HRq σ p l rr);
        [apply HSσ; exact Hσ|exact Hpl|exact Hll|exact Hr].
    - intros σ p Hσ Hpl Hk. apply (HKq σ p);
        [apply HSσ; exact Hσ|exact Hpl|exact Hk]. }
  apply (under_denote_intro_store_coverage gasout Σ TTree Θ _ m S);
    [exact Hlc|exact Hzero| |].
  - intros y Hy σ Hσ.
    destruct (Hinhabited y (store_restrict σ S) Hy
      ltac:(change (dom (storeA_restrict σ S : gmap atom value) = S);
        rewrite storeA_restrict_dom, (wfworld_store_dom m σ Hσ);
        clear -HSm; set_solver)) as [τ [Hτ HτS]].
    exists τ. split; [exact Hτ|]. rewrite DΘ. exact HτS.
  - intros y Hy σ τ Hσ HτS Hτq.
    destruct (Htarget y τ Hy Hτq) as [t [Hty HQt]].
    rewrite DΘ in HτS. rewrite HτS in HQt.
    destruct (Hcoverage σ t Hσ HQt) as [σ' [Hσ' [Hσ'S Heval]]].
    exists σ', (vconst (ctree t)). split; [exact Hσ'|].
    split; [rewrite DΘ; exact Hσ'S|]. split; assumption.
Qed.
