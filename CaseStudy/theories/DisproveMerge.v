(** * DisproveMerge specifications

    Extracted from CaseStudy/theories/DisproveMerge.v at cd3eace.
    Only semantic predicates, qualifiers, and type definitions are included. *)

From CaseStudy Require Import CaseTypes.
From Stdlib Require Import List.

Import ListNotations.
Open Scope core_scope.
Open Scope cty_scope.

Fixpoint mem_list (n : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => False
  | x :: xs => n = x \/ mem_list n xs
  end.

Fixpoint sorted_from (prev : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs => prev <= x /\ sorted_from x xs
  end.

Definition sorted (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs => sorted_from x xs
  end.

Definition q_sorted_list (v : value) : type_qualifier :=
  q_list_pred v sorted.

Definition q_not_sorted_list (v : value) : type_qualifier :=
  q_list_pred v (fun xs => ~ sorted xs).

Definition OSortedList : context_ty :=
  over_ty TList (q_sorted_list ν).

Definition UNotSortedList : context_ty :=
  under_ty TList (q_not_sorted_list ν).

Definition merge_basic_ty : ty :=
  List →ᵦ List →ᵦ List.

Definition le_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition merge_safety_ty : context_ty :=
  OSortedList → OSortedList → OSortedList.

Definition merge_disprove_ty : context_ty :=
  O[ List ] → O[ List ] → OSortedList ⊕ UNotSortedList.
