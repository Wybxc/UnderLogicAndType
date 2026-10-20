# Verified case studies

This directory contains context-typing proofs for three case studies. Each
entry below has a derivation of `has_context_type` and a denotational-soundness
corollary obtained from `concrete_Fundamental`.

## Directory

| Case study | Program and specification | Main proof entry |
| --- | --- | --- |
| [May/must analysis](#maymust-analysis-figure-6) — revised Fig. 6(a–b) | [MayMustRevised.v](theories/MayMustRevised.v) | [MayMustIndependentTyping.v](theories/MayMustIndependentTyping.v) (a), [MayMustTyping.v](theories/MayMustTyping.v) (b) |
| [BST generator](#bst-generator-figure-7) — corrected Fig. 7 | [BSTGeneratorProgram.v](theories/BSTGeneratorProgram.v), [BSTGenerator.v](theories/BSTGenerator.v) | [BSTGeneratorContextTyping.v](theories/BSTGeneratorContextTyping.v) |
| [Incorrectness reasoning](#incorrectness-reasoning-figure-8) — revised Fig. 8, pp. 24–25 | [MergeProgram.v](theories/MergeProgram.v), [MergeIncorrectness.v](theories/MergeIncorrectness.v) | [MergeWorkerTyping.v](theories/MergeWorkerTyping.v) |

## Checking the proofs

First install the locked dependencies using the repository's
[environment setup instructions](../README.md#compilation-and-dependencies).
Run all commands below **from the repository root**.

Generate the Makefile, then compile the four proof entries covering all three
case studies. Their dependencies are built automatically.

```sh
opam exec -- rocq makefile -f _CoqProject -o Makefile
opam exec -- make -j4 \
  CaseStudy/theories/MayMustIndependentTyping.vo \
  CaseStudy/theories/MayMustTyping.vo \
  CaseStudy/theories/BSTGeneratorContextTyping.vo \
  CaseStudy/theories/MergeWorkerTyping.vo
```

To build the entire project instead, run `opam exec -- make -j4` after
generating the Makefile.

After compilation, independently recheck the compiled proofs and their
imported dependencies with the Rocq kernel checker:

```sh
opam exec -- rocq check -silent $(awk '/^-R/{print}' _CoqProject) \
  CaseStudy.MayMustIndependentTyping \
  CaseStudy.MayMustTyping \
  CaseStudy.BSTGeneratorContextTyping \
  CaseStudy.MergeWorkerTyping
```

With `-silent`, a successful check exits with status 0 and produces no output.
To inspect the theorem statements and their logical assumptions:

```sh
opam exec -- rocq top -quiet $(awk '/^-R/{print}' _CoqProject) <<'EOF'
From CaseStudy Require Import MayMustIndependentTyping MayMustTyping
  BSTGeneratorContextTyping MergeWorkerTyping.
Check may_help_must_context_typed.
Check must_help_may_context_typed.
Check bst_gen_type_judgement_holds.
Check merge_worker_incorrect_context_typed.
Print Assumptions may_help_must_context_typed.
Print Assumptions must_help_may_context_typed.
Print Assumptions bst_gen_type_judgement_holds.
Print Assumptions merge_worker_incorrect_context_typed.
EOF
```

These proofs use the project's existing classical logic, indefinite
description, extensionality, and proof-irrelevance assumptions; they should
not be read as axiom-free results. For interactive checking, follow the
[VS Code / VS Rocq setup](../README.md#vs-code--vs-rocq) and open the main
proof files listed above.

## May/must analysis (Figure 6)

Both examples use native integers and an arbitrary free function `g` satisfying
its stated context type. The proofs type the programs under that assumption;
they do not assume a particular implementation of `g`.

| Example | Context-typing theorem | Fundamental corollary |
| --- | --- | --- |
| Fig. 6(a), `may_help_must g` | `may_help_must_context_typed` | `may_help_must_context_sound` |
| Fig. 6(b), `must_help_may g` | `must_help_may_context_typed` | `must_help_may_context_sound` |

**Variant:** Fig. 6(a) tests `y >= 10`, as requested, rather than the paper's
`y > 10`. Its result remains the specified Under type for `1`, with an
independent second argument. Fig. 6(b) establishes the sum of the Over types
for `2` and `5`.

See [MayMustFormalization.md](MayMustFormalization.md) for the specifications
and proof details.

## BST generator (Figure 7)

The closed term `bst_gen_program` has the full persistent type `bst_gen_ty`.
Its Under result covers trees satisfying the strict BST predicate and exact
membership condition `tree_mem n t <-> lo < n <= lo + r`.

The corrected persistent range-function contract uses `x <= y` as its domain
condition and both Over and Under results for `x <= ν <= y`. In particular,
`range 1 r` is valid at `r = 1`.

In [BSTGeneratorContextTyping.v](theories/BSTGeneratorContextTyping.v):

- `bst_gen_context_typed` proves the context-typing judgment.
- `bst_gen_type_judgement_holds` proves the named target proposition
  `bst_gen_type_judgement` from `BSTGeneratorProgram.v`.
- `bst_gen_denotational_sound` is the Fundamental corollary.

For the proof route, read [BSTPositiveTyping.v](theories/BSTPositiveTyping.v)
(the positive branch), [BSTCallTyping.v](theories/BSTCallTyping.v)
(induction over call sizes), then the main proof entry.

## Incorrectness reasoning (Figure 8)

The original recursive value `IncorrectMerge.merge_value` has the complete
independent-arrow specification `merge_incorrect_ty`: independent inputs
covering sorted lists expose an unsorted output through the result sum.
The main theorem types the original fixed-point value directly, without an
explicit η-expanded wrapper.

In [MergeWorkerTyping.v](theories/MergeWorkerTyping.v):

- `merge_worker_incorrect_context_typed` proves the context-typing judgment.
- `merge_worker_incorrect_context_sound` is the Fundamental corollary.

[MergeTraceTyping.v](theories/MergeTraceTyping.v) also proves the worker's
precise ordinary-arrow type and the finite-trace type on p. 25.
[MergeReduction.v](theories/MergeReduction.v) proves exact execution and must
termination, including `merge [1;2] [3;4] →* [1;3;2;4]`.
The external caller using `sorted_list_gen` on p. 25 is not yet given a
context-typing derivation.

See [IncorrectnessFormalization.md](IncorrectnessFormalization.md) for the
specifications, independence requirements, and proof route.

## Shared support and other modules

- [CaseTypes.v](theories/CaseTypes.v) provides shared specification helpers.
- [NatArithmeticTyping.v](theories/NatArithmeticTyping.v) proves
  `add_value_context_typed` and `sub_value_context_typed`, including persistence
  and exact natural-number results. These library proofs support the BST case.
- [AddedTypingRules.md](AddedTypingRules.md) lists the added typing rules in
  LaTeX notation. Their soundness proofs are connected to `Fundamental`.
- `Section1Intro.v`, `Section2Typing.v`, `Section3Logic.v`, and
  `Section4Extension.v` retain introductory specifications. `MayMust.v` and
  `DisproveMerge.v` retain older specifications; use the entries above for the
  proved revised examples.
- [SemanticsAudit.md](SemanticsAudit.md) and
  [Example33Counterexample.md](Example33Counterexample.md) discuss the original
  `CT_Fix` mixed-world limitation. The case-study proofs leave that rule and
  the type denotation unchanged.
