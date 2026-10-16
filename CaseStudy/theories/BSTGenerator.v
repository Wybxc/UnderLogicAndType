(** * BSTGenerator specifications

    Adapted from CaseStudy/theories/BSTGenerator.v at cd3eace.
    The generator takes a size [r], a lower bound [lo], and a persistent
    exact closed-interval range function. Its under-approximate result
    specification covers strict BSTs whose members are exactly the natural
    numbers in [(lo, lo + r]]. *)

From CaseStudy Require Import CaseTypes.
From ContextTypeLanguage Require Import WF.
From Stdlib Require Import List.

Import ListNotations.
Open Scope core_scope.
Open Scope cty_scope.

Fixpoint tree_mem (n : nat) (t : tree) : Prop :=
  match t with
  | tr_leaf => False
  | tr_node r l rr => n = r \/ tree_mem n l \/ tree_mem n rr
  end.

Fixpoint bst_between (lo hi : nat) (t : tree) : Prop :=
  match t with
  | tr_leaf => True
  | tr_node r l rr =>
      lo <= r < hi /\
      bst_between lo r l /\
      bst_between (S r) hi rr
  end.

(** [bst_between] uses [lower, upper), so successors encode (lo, lo + r].
    Both subtrees are strict: duplicate keys are excluded. *)
Definition bst_spec (r lo : nat) (t : tree) : Prop :=
  bst_between (S lo) (S (lo + r)) t /\
  (forall n : nat, tree_mem n t <-> lo < n <= lo + r).

Definition q_tree_bst_range (r lo t : value) : type_qualifier :=
  tqual (lvar_value_keys r ∪ lvar_value_keys lo ∪ lvar_value_keys t)
    (fun σ =>
       exists nr nlo tr,
         denote_lvar_value (lso_store σ) r = Some (vconst (cnat nr)) /\
         denote_lvar_value (lso_store σ) lo = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) t = Some (vconst (ctree tr)) /\
         bst_spec nr nlo tr).

Definition q_mem_tree_iff_range (r lo t : value) : type_qualifier :=
  tqual (lvar_value_keys r ∪ lvar_value_keys lo ∪ lvar_value_keys t)
    (fun σ =>
       exists nr nlo tr,
         denote_lvar_value (lso_store σ) r = Some (vconst (cnat nr)) /\
         denote_lvar_value (lso_store σ) lo = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) t = Some (vconst (ctree tr)) /\
         forall n, tree_mem n tr <-> nlo < n <= nlo + nr).

(** In the final result qualifier: arg2 = r, arg1 = lo, arg0 = range. *)
Definition OBstBetween : context_ty :=
  over_ty TTree (q_tree_bst_range arg2 arg1 ν).

Definition UBstBetween : context_ty :=
  under_ty TTree (q_tree_bst_range arg2 arg1 ν).

Definition bst_range_pred := bst_between.

Definition bst_generator_spec := bst_spec.

Definition q_nat_lt (a b : value) : type_qualifier :=
  tqual (lvar_value_keys a ∪ lvar_value_keys b)
    (fun σ => exists na nb : nat,
      denote_lvar_value (lso_store σ) a = Some (vconst (cnat na)) /\
      denote_lvar_value (lso_store σ) b = Some (vconst (cnat nb)) /\
      na < nb).

Definition q_nat_le (a b : value) : type_qualifier :=
  tqual (lvar_value_keys a ∪ lvar_value_keys b)
    (fun σ => exists na nb : nat,
      denote_lvar_value (lso_store σ) a = Some (vconst (cnat na)) /\
      denote_lvar_value (lso_store σ) b = Some (vconst (cnat nb)) /\
      na <= nb).

(** The y-domain refers to x as arg0. The result refers to x as arg1
    and y as arg0; ν is the value being refined in each case.
    Closed endpoints make [range 1 r] valid also when r = 1. Precision
    requires all outputs to stay in the interval and every point to be
    reachable, providing both recursive decrease and coverage. *)
Definition range_ty : context_ty :=
  □ (O[ ℕ ] →
     over_ty TNat (q_nat_le arg0 ν) →
     precise_ty TNat
       (qual_and (q_nat_le arg1 ν) (q_nat_le ν arg0))).

Definition bst_gen_ty : context_ty :=
  □ (O[ ℕ ] → O[ ℕ ] → range_ty → UBstBetween).

Definition bst_gen_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree.

Lemma bst_gen_ty_well_formed : basic_context_ty ∅ bst_gen_ty.
Proof.
  cbn [basic_context_ty wf_context_ty_at bst_gen_ty range_ty UBstBetween
    over_ty under_ty precise_ty q_nat_le q_tree_bst_range
    qual_and qual_vars qual_top_on arg0 arg1 arg2 vnu lvar_value_keys
    erase_ty].
  unfold lvars_wf_at.
  repeat split; try reflexivity.
  all: intros [k | x] H; cbn [lvar_wf_at].
  all: cbn in H.
  all: set_solver by lia.
Qed.
