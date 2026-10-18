(** Closed integer refinements: store-level introduction and elimination.
    All typing consequences below use existing declarative rules. *)
From CaseStudy Require Import MayMustRevised MayMustWorlds.
From Denotation Require Import Context ResultQualifier ConditionalCoverage
  BaseCoverage OverConsequence TypeEquiv TypeEquivCore ConstDenote.
From ContextTyping Require Import Typing TypingRegular Subtyping BasicBindings
  NatCases ConstCases SoundnessLam PrimOpConcreteContext.
From Stdlib Require Import ZArith.

Lemma int_pred_open_store P y s :
  qualifier_holds_store (qual_open_atom 0 y (int_pred P)) s <->
  exists z, s !! y = Some (vint z) /\ P z.
Proof.
  unfold int_pred. rewrite param_result_qual_open_store by set_solver.
  split.
  - intros [_ [v [Hv [_ [z [-> Hz]]]]]]. eauto.
  - intros [z [Hz HP]]. split; [set_solver|].
    exists (vint z). repeat split; try assumption. apply BVT_Const.
    exists z. auto.
Qed.

Lemma int_pred_typed P : typed_result_qual TInt (int_pred P) = int_pred P.
Proof. apply typed_param_result_qual. Qed.

Lemma int_bind_under_covers x P (m : WfWorldT) z :
  m ⊨ ctx_denote_under ∅ (CtxBind x (UInt P)) -> P z ->
  exists s, (m : WorldT) s /\ s !! x = Some (vint z).
Proof.
  intros Hctx HP. rewrite ctx_denote_closed_bind in Hctx by apply (int_pred_fv false).
  apply res_models_and_iff in Hctx as [_ Hden].
  destruct (world_wf m) as [[s Hs] _].
  destruct (under_ret_var_covers_value 0
    (atom_env_to_lty_env {[x:=TBase TInt]}) TInt (int_pred P) x m s (vint z)
    (atom_store_to_lvar_store_closed _) ltac:(rewrite int_pred_dom; set_solver)
    Hden Hs) as [t [Ht [_ Htx]]].
  - rewrite int_pred_typed, int_pred_open_store. exists z. split;
      [apply map_lookup_insert|exact HP].
  - eauto.
Qed.

Lemma int_bind_over_holds x P (m : WfWorldT) :
  m ⊨ ctx_denote_under ∅ (CtxBind x (OInt P)) ->
  forall s, (m : WorldT) s -> exists z, s !! x = Some (vint z) /\ P z.
Proof.
  intros Hctx s Hs. rewrite ctx_denote_closed_bind in Hctx by apply (int_pred_fv true).
  apply res_models_and_iff in Hctx as [_ Hden].
  pose proof (over_ret_var_store_holds 0
    (atom_env_to_lty_env {[x:=TBase TInt]}) TInt (int_pred P) x m
    (atom_store_to_lvar_store_closed _) ltac:(rewrite int_pred_dom; set_solver)
    Hden s Hs) as Hq.
  rewrite int_pred_typed,int_pred_open_store in Hq. exact Hq.
Qed.

Lemma int_bind_static_guard x P pol (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=TBase TInt]}) ->
  m ⊨ ty_denote_gas 0 (atom_env_to_lty_env {[x:=TBase TInt]})
    (match pol with true => OInt P | false => UInt P end) (tret (vfvar x)).
Proof.
  intros Hworld.
  pose proof (over_top_bind_denote_from_basic_world x TInt m Hworld) as Htop.
  rewrite ctx_denote_closed_bind in Htop by
    (pose proof (basic_context_ty_fv_subset ∅ _ (over_top_basic TInt)); set_solver).
  apply res_models_and_iff in Htop as [_ Htop].
  destruct pol; apply ty_denote_gas_zero_tret_of_static_guard;
    apply context_typing_wf_denot_static_guard_full with
      (Σ:=∅) (Γ:=CtxBind x (CTOver TInt qual_top)).
  all: try (rewrite ctx_denote_closed_bind by
      (pose proof (basic_context_ty_fv_subset ∅ _ (over_top_basic TInt)); set_solver);
      apply res_models_and_iff; auto).
  all: split; [split; [set_solver|apply over_top_basic]|]; split;
    [first [apply int_pred_over_wf|apply int_pred_wf]|
      apply TT_Ret, VT_FVar; apply map_lookup_singleton].
Qed.

Lemma int_bind_over_intro x P (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=TBase TInt]}) ->
  (forall s, (m : WorldT) s -> exists z, s !! x = Some (vint z) /\ P z) ->
  m ⊨ ctx_denote_under ∅ (CtxBind x (OInt P)).
Proof.
  intros Hworld HP. rewrite ctx_denote_closed_bind by apply (int_pred_fv true).
  apply res_models_and_iff. split; [exact Hworld|].
  apply (over_denote_intro_store_results 1 _ TInt (int_pred P) _ m ∅).
  - eapply (basic_context_ty_lc ∅). apply int_pred_over_wf.
  - exact (int_bind_static_guard x P true m Hworld).
  - intros y _ s v Hs Heval.
    destruct (HP s Hs) as [z [Hz HPz]].
    assert (Heq : v = vint z).
    { unfold tm_eval_in_store,expr_eval_in_store in Heval.
      rewrite (instantiate_ret_const_var s x (cint z) Hz) in Heval.
      pose proof (val_steps_self _ _ Heval). unfold vint. congruence. }
    subst v. rewrite int_pred_typed,int_pred_open_store.
    exists z. split; [apply map_lookup_insert|exact HPz].
Qed.

Lemma int_bind_under_intro x P (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env {[x:=TBase TInt]}) ->
  (exists z, P z) ->
  (forall z, P z -> exists s, (m : WorldT) s /\ s !! x = Some (vint z)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind x (UInt P)).
Proof.
  intros Hworld [z0 HP0] Hcover.
  rewrite ctx_denote_closed_bind by apply (int_pred_fv false).
  apply res_models_and_iff. split; [exact Hworld|].
  apply (under_denote_intro_store_coverage 1 _ TInt (int_pred P) _ m ∅).
  - eapply (basic_context_ty_lc ∅). apply int_pred_wf.
  - exact (int_bind_static_guard x P false m Hworld).
  - intros y _ s Hs. exists (<[y:=vint z0]> s). split.
    + rewrite int_pred_typed,int_pred_open_store. exists z0.
      split; [apply map_lookup_insert|exact HP0].
    + rewrite int_pred_dom,!storeA_restrict_empty_set. reflexivity.
  - intros y _ s t Hs Hproj Hq.
    rewrite int_pred_typed,int_pred_open_store in Hq.
    destruct Hq as [z [Hzy HPz]].
    destruct (Hcover z HPz) as [s' [Hs' Hxz]].
    exists s', (vint z). split; [exact Hs'|]. split.
    + rewrite int_pred_dom,!storeA_restrict_empty_set. reflexivity.
    + split; [exact Hzy|]. unfold tm_eval_in_store,expr_eval_in_store.
      rewrite (instantiate_ret_const_var s' x (cint z) Hxz).
      apply value_reduction_any_ctx. constructor.
Qed.

Lemma int_pred_singleton z :
  int_pred (fun n => n = z) = mk_q_eq (vbvar 0) (vint z).
Proof.
  apply qual_ext.
  - cbn [int_pred param_result_qual mk_q_eq lvar_value_keys qual_lvars
      lvars_of_atoms]. set_solver.
  - intros [s1 Hd1] [s2 Hd2] Hs.
    cbn [lso_store storeAO_store] in Hs.
    cbn [int_pred param_result_qual mk_q_eq lvar_value_keys qual_prop
      qual_lvars lso_store storeAO_store denote_lvar_value].
    rewrite Hs. split.
    + intros [v [Hv [_ [n [-> ->]]]]]. exact Hv.
    + intros Hv. exists (vint z). split; [exact Hv|].
      split; [apply BVT_Const|]. exists z. auto.
Qed.

Lemma typing_int_const Φ Σ Γ z :
  wf_ctx_under Σ Γ ->
  has_context_type Φ Σ Γ (tret (vint z)) (OInt (fun n => n = z)).
Proof.
  intros HΓ. unfold OInt. rewrite int_pred_singleton.
  change (has_context_type Φ Σ Γ (tret (vconst (cint z)))
    (CTOver (base_ty_of_const (cint z)) (mk_q_eq (vbvar 0) (vconst (cint z))))).
  apply typing_inter_l with
    (τ2:=CTUnder TInt (mk_q_eq (vbvar 0) (vint z))).
  apply typing_const_in_ctx. split; [exact HΓ|].
  split; [apply const_precise_wf|apply TT_Ret, VT_Const].
Qed.

Lemma mm_comma_closed_right Σ Γ x τ (m : WfWorldT) :
  fv_cty τ = ∅ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x τ)) ->
  m ⊨ ctx_denote_under ∅ (CtxBind x τ).
Proof.
  intros Hclosed Hctx. cbn [ctx_denote_under] in Hctx.
  apply res_models_and_iff in Hctx as [_ Hctx].
  apply res_models_and_iff in Hctx as [_ Hright].
  rewrite ctx_denote_closed_bind by exact Hclosed.
  cbn [ctx_fv] in Hright. rewrite Hclosed, storeA_restrict_empty_set in Hright.
  unfold store_union,store_empty in Hright. rewrite map_empty_union in Hright.
  exact Hright.
Qed.

Lemma mm_comma_over_store Σ Γ x b φ (m : WfWorldT) :
  x ∉ qual_dom φ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x (CTOver b φ))) ->
  forall s, (m : WorldT) s ->
    qualifier_holds_store (qual_open_atom 0 x (typed_result_qual b φ)) s.
Proof.
  intros Hx Hctx. cbn [ctx_denote_under] in Hctx.
  apply res_models_and_iff in Hctx as [_ Hbody].
  apply res_models_and_iff in Hbody as [_ Hbind].
  apply res_models_and_iff in Hbind as [_ Hden].
  eapply (over_ret_var_store_holds 0 _ b φ x m);
    [apply atom_store_to_lvar_store_closed|exact Hx|exact Hden].
Qed.
