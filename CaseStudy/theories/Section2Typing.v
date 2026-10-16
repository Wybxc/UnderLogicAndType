(** * Section2Typing specification types

    Extracted from CaseStudy/theories/Section2Typing.v at cd3eace.
    Program terms, typing derivations, and subtyping obligations are omitted. *)

From CaseStudy Require Import CaseTypes.

Open Scope core_scope.
Open Scope cty_scope.

Definition nat_to_nat_ty : ty := (ℕ : ty) →ᵦ ℕ.

Definition nat_to_nat_to_nat_ty : ty := (ℕ : ty) →ᵦ ℕ →ᵦ ℕ.

Definition may_must_intro_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ ℕ.
