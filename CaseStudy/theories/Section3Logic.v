(** * Section3Logic specification types

    Extracted from CaseStudy/theories/Section3Logic.v at cd3eace.
    Program terms, typing derivations, and subtyping obligations are omitted. *)

From CaseStudy Require Import CaseTypes.

Open Scope core_scope.
Open Scope cty_scope.

Definition nat_increment_ty : ty := (ℕ : ty) →ᵦ ℕ.
