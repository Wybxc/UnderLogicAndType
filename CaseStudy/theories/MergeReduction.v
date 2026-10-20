(** Deterministic reductions, including termination. No new primitive or rule. *)
From CaseStudy Require Export MergeProgram.
From ContextTyping Require Import Conversion.
From CoreLang Require Import SyntaxRegular.
Import ListNotations.

Lemma merge_prefix_trans e e' e'' :
  arithmetic_prefix e e' -> arithmetic_prefix e' e'' -> arithmetic_prefix e e''.
Proof. induction 1; intros Hnext; [exact Hnext|econstructor; eauto]. Qed.
Lemma merge_run_prefix e v : arithmetic_run e v -> arithmetic_prefix e (tret v).
Proof. induction 1; [constructor|econstructor; eauto]. Qed.
Lemma merge_prefix_let e e' b :
  arithmetic_prefix e e' -> lc_tm (tlete e b) ->
  arithmetic_prefix (tlete e b) (tlete e' b).
Proof.
  induction 1 as [e|e e' e'' [Hs Hd] Hp IH]; intros Hlc; [constructor|].
  eapply Prefix_step with (e':=tlete e' b).
  - apply arithmetic_certified_let; [split; assumption|exact Hlc].
  - apply IH. eapply step_regular2. apply Step_let; eauto.
Qed.
Ltac merge_lc_from h :=
  first [exact h | lazymatch type of h with
    | lc_tm (tlete _ _) => let h':=fresh in pose proof (proj1 (proj1 (lc_lete_iff_body _ _) h)) as h'; merge_lc_from h'
    end].
Ltac merge_lc := first [assumption | match goal with H : lc_tm _ |- _ => solve [merge_lc_from H] end |
  eapply (basic_typing_regular_tm ∅); type_merge].
Ltac merge_head :=
  first [apply HS_Ret|apply HS_Beta|apply HS_Fix|apply HS_MatchTrue|apply HS_MatchFalse|
    apply HS_ListCons|apply HS_MatchListNil|apply HS_MatchListCons|
    (apply HS_Op; [constructor|])]; merge_lc.
Ltac merge_step :=
  lazymatch goal with
  | |- step (tlete (tret _) _) _ /\ _ =>
    split; [apply Step_head; merge_head|eapply arithmetic_head_deterministic;
      [merge_head|let heq:=fresh "heq" in intros op c heq; discriminate]]
  | |- step (tlete _ _) _ /\ _ => apply arithmetic_certified_let; [merge_step|merge_lc]
  | |- step _ _ /\ _ =>
    split; [apply Step_head; merge_head|eapply arithmetic_head_deterministic;
      [merge_head|let heq:=fresh "heq" in intros op c heq; inversion heq; subst; split; discriminate]]
  end.
Ltac merge_eval :=
  lazymatch goal with |- arithmetic_prefix ?e ?target =>
    let e':=eval cbv -[Nat.sub Nat.eqb IncorrectMerge.result] in e in
    change (arithmetic_prefix e' target)
  end;
  repeat match goal with H : ?v = ?b |- _ =>
    is_constructor b; progress rewrite H
  end.
Fixpoint merge_next (e : tm) : tm :=
  match e with
  | tlete (tret v) body => open_tm 0 v body
  | tlete e body => tlete (merge_next e) body
  | tapp (vlam _ body) v => open_tm 0 v body
  | tapp (vfix tf body) v => tapp (open_value 0 v body) (vfix tf body)
  | tprim op_eq0 (vconst (cnat n)) => tret (vconst (cbool (Nat.eqb n 0)))
  | tprim op_minus1 (vconst (cnat n)) => tret (vnat (Nat.pred n))
  | tprim op_plus1 (vconst (cnat n)) => tret (vnat (S n))
  | tmatch (vconst (cbool true)) et ef => et
  | tmatch (vconst (cbool false)) et ef => ef
  | tcons (vconst (cnat n)) (vconst (clist xs)) => tret (IncorrectMerge.vlist (n::xs))
  | tmatchlist (vconst (clist [])) en ec => en
  | tmatchlist (vconst (clist (n::xs))) en ec => open_list_cons_branch_value (vnat n) (IncorrectMerge.vlist xs) ec
  | _ => e
  end.
Ltac merge_one :=
  merge_eval;
  lazymatch goal with |- arithmetic_prefix ?e ?target =>
    let reduct:=eval cbv -[Nat.sub Nat.eqb IncorrectMerge.result] in (merge_next e) in
    let cert:=fresh "cert" in
    assert (cert : step e reduct /\ forall z,step e z->z=reduct) by merge_step;
    eapply Prefix_step with (e':=reduct); [exact cert|];
    pose proof (step_regular2 _ _ (proj1 cert))
  end.
Ltac merge_normalize IH :=
  first [apply Prefix_refl |
    eapply merge_prefix_trans;
      [apply merge_prefix_let; [apply merge_run_prefix,sub_value_run|merge_lc]|];
      merge_eval; merge_normalize IH |
    merge_one; merge_normalize IH].

Lemma merge_call_prefix xs ys :
  arithmetic_prefix (IncorrectMerge.call xs ys)
    (tret (IncorrectMerge.vlist (IncorrectMerge.result xs ys))).
Proof.
  revert ys. induction xs as [|a xs IH]; intros [|b ys]; lazymatch goal with |- arithmetic_prefix (IncorrectMerge.call ?xx ?yy) _ => pose proof (basic_typing_regular_tm ∅ _ _ (merge_call_basic xx yy)) end.
  - merge_normalize IH.
  - merge_normalize IH.
  - merge_normalize IH.
  - unfold IncorrectMerge.call at 1.
    (* Stop before the recursive call, keeping its syntax available to IH. *)
    eapply merge_prefix_trans with
      (e':=tlete (IncorrectMerge.call xs ys)
        (match IncorrectMerge.body (IncorrectMerge.vlist (a::xs)) (IncorrectMerge.vlist (b::ys)) with
         | tmatchlist _ _ ec =>
           match open_list_cons_branch_value (vnat b) (IncorrectMerge.vlist ys) ec with
           | tmatchlist _ _ ec' =>
             match open_list_cons_branch_value (vnat a) (IncorrectMerge.vlist xs) ec' with
             | tlete _ cont => cont | _ => tret (vconst cunit) end
           | _ => tret (vconst cunit) end
         | _ => tret (vconst cunit) end)).
    + let target:=match goal with |- arithmetic_prefix _ ?t => constr:(t) end in
      lazymatch goal with |- arithmetic_prefix ?e _ => let e':=eval vm_compute in e in change (arithmetic_prefix e' target) end.
      do 6 merge_one. apply Prefix_refl.
    + eapply merge_prefix_trans; [apply merge_prefix_let; [apply IH|merge_lc]|].
      cbn [IncorrectMerge.result].
      (* Normalize the finite suffix with symbolic heads using the library. *)
      destruct (Nat.eqb (b-a) 0) eqn:Hba; destruct (Nat.eqb (a-b) 0) eqn:Hab;
      rewrite ?Hba,?Hab; merge_normalize IH.
Qed.

Lemma merge_call_body_prefix xs ys :
  arithmetic_prefix (IncorrectMerge.call xs ys)
    (IncorrectMerge.body (IncorrectMerge.vlist xs) (IncorrectMerge.vlist ys)).
Proof.
  pose proof (basic_typing_regular_tm ∅ _ _ (merge_call_basic xs ys)).
  do 4 merge_one. apply Prefix_refl.
Qed.

Lemma merge_trace_empty : IncorrectMerge.result [] [] = []. Proof. reflexivity. Qed.
Lemma merge_trace_singletons : IncorrectMerge.result [2] [4] = [2;4]. Proof. reflexivity. Qed.
Lemma merge_trace_bug : IncorrectMerge.result [1;2] [3;4] = [1;3;2;4]. Proof. reflexivity. Qed.
Lemma merge_trace_unsorted : ~ sorted [1;3;2;4]. Proof. cbn [sorted sorted_from]; lia. Qed.

(** The subtraction tests implement exactly the comparisons in Fig.8. *)
Lemma merge_result_cons a b xs ys :
  IncorrectMerge.result (a::xs) (b::ys) =
  match Nat.ltb a b with
  | true => a::b::IncorrectMerge.result xs ys
  | false => match Nat.ltb b a with
    | true => b::a::IncorrectMerge.result xs ys
    | false => a::IncorrectMerge.result xs ys end
  end.
Proof.
  cbn [IncorrectMerge.result].
  destruct (Nat.eqb (b-a) 0) eqn:Hba; destruct (Nat.eqb (a-b) 0) eqn:Hab;
    destruct (a <? b) eqn:Hlt; destruct (b <? a) eqn:Hgt;
    try reflexivity;
    first [apply Nat.eqb_eq in Hba|apply Nat.eqb_neq in Hba];
    first [apply Nat.eqb_eq in Hab|apply Nat.eqb_neq in Hab];
    first [apply Nat.ltb_lt in Hlt|apply Nat.ltb_ge in Hlt];
    first [apply Nat.ltb_lt in Hgt|apply Nat.ltb_ge in Hgt]; lia.
Qed.

(** The correlated caller on p.25 has complete marginal coverage but never
    supplies two nonempty inputs. This is a relation check, not a typing
    derivation for the caller's external sorted-list generator. *)
Definition merge_masked_inputs xs ys := sorted xs /\ sorted ys /\ (xs=[] \/ ys=[]).
Lemma merge_masked_left_covers xs : sorted xs -> exists ys, merge_masked_inputs xs ys.
Proof. intros H. exists []. unfold merge_masked_inputs. split; [exact H|]. split; [exact I|right; reflexivity]. Qed.
Lemma merge_masked_right_covers ys : sorted ys -> exists xs, merge_masked_inputs xs ys.
Proof. intros H. exists []. unfold merge_masked_inputs. split; [exact I|]. split; [exact H|left; reflexivity]. Qed.
Lemma merge_masked_result_sorted xs ys :
  merge_masked_inputs xs ys -> sorted (IncorrectMerge.result xs ys).
Proof.
  intros [Hx [Hy [-> | ->]]]; [destruct ys|destruct xs]; assumption || exact I.
Qed.
