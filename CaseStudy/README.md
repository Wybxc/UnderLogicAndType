# Case-study specifications

These modules extract specification definitions from
`codex/core-tree-extension` at commit
`cd3eace61c92d8a2d3eb708b5c22c4d3127cc91f`.

| Module | Definitions |
| --- | --- |
| `CaseTypes` | Shared type aliases, notation, and semantic qualifier constructors |
| `Section1Intro` | Basic function types for the introduction examples |
| `Section2Typing` | Basic function types for the typing examples |
| `Section3Logic` | The increment function's basic type |
| `Section4Extension` | Boolean-to-natural and Boolean-to-Boolean function types |
| `MayMust` | Figure 5.1 may/must summary types and their natural-number predicates |
| `BSTGenerator` | BST/range predicates, qualifiers, and generator types |
| `NatArithmetic` | Unary-core addition and truncated subtraction, exact execution and termination proofs, and precise context-type specifications |
| `BSTGeneratorProgram` | Corrected Fig. 7 core program, target context-typing judgment, and checked basic typing |
| `DisproveMerge` | List membership/sortedness predicates and merge safety/disproof types |

The imported definitions retain their original names and bodies, except for
`BSTGenerator`: its specification now describes a persistent function taking
`r`, `lo`, and a persistent range function. The corrected range contract has
an over-approximate domain `x <= y` and a precise result
`{ν : nat | x <= ν <= y} ⊓ [ν : nat | x <= ν <= y]`. Thus `range 1 r`
is valid when `r = 1`, every result stays within the closed interval, and
every point in that interval is reachable.
The generator has an under-approximate tree result satisfying the BST
predicate and `tree_mem n t <-> lo < n <= lo + r`. Its result qualifier uses
`arg2` for `r` and `arg1` for `lo`; the nearest argument is the range function.
The BST predicate excludes duplicate keys in both subtrees.

`BSTGeneratorProgram` encodes the corrected generator using the existing
locally nameless core syntax. It imports the addition and truncated-subtraction
library from `NatArithmetic`; `boolGen` implements
nondeterministic choice. Its exported `bst_gen_program` is closed and has
the basic type obtained by erasing `bst_gen_ty`; these properties are proved.
The specification's well-formedness is also proved.

`bst_gen_type_judgement` defines the target proposition
`has_context_type concrete_Φ ∅ CtxEmpty bst_gen_program bst_gen_ty`.
This proposition is not asserted as a theorem: a context-typing derivation
still needs sound support for tree construction and the recursion, arithmetic,
and coverage arguments.
Other example programs, context-typing derivations, semantic-subtyping proof
obligations, and the binary-operation result qualifiers used by those
obligations are omitted. The shared
specification helpers come from the source branch's
`ProofAutomation/theories/CaseTypes.v`; they import the existing syntax
directly and do not depend on `ProofAutomation`.

Tree/List support is integrated into the STLC core using the source branch's
Tree/List changes through commit `bfea370efa04c54af1b22e84863c99415a2a1109`.
The extension includes constants, construction and matching terms, basic
typing, operational semantics, locally nameless operations, and the proofs
needed to keep the existing metatheory checked. The current `Unit` support
is retained. The corresponding logical-variable basic-typing judgments and
denotation support are updated to cover these STLC terms.

`ContextTyping/theories/Typing.v` now additionally supports dependent lookup of
the final additive binding (`CT_VarR`) and exact base-variable returns
(`CT_VarSelf`). Both rules are proved sound in `SoundnessVar` and included in
`Fundamental`. Reading earlier bindings is derived using the existing
`CT_CtxSub` rule (`typing_weaken_comma`); it is not a new primitive rule.
The source branch's `ExtendedTyping`, `ExtendedSubsumption`, inference
automation, and binary-operation language extension are not imported.

`NatArithmetic.add_value_run` and `sub_value_run` prove deterministic execution
for all natural inputs. Their corollaries prove both must termination and the
exact result sets: respectively `{n + m}` and `{n - m}`, where subtraction is
truncated at zero. The proofs follow the original small-step semantics and
do not introduce primitive binary operations. `add_context_ty` and
`sub_context_ty` specify persistent functions with precise results
`ν = a + b` and `ν = a - b`; their well-formedness and erasures are proved.
`NatArithmeticTyping.add_value_context_typed` and
`sub_value_context_typed` now prove the corresponding `has_context_type`
judgments for both function values, including the outer persistence modality.
They are polymorphic in the primitive-operation context `Φ`, since these
library functions use no primitive-operation typing assumptions.

The derivation has three checked parts:

- `NatArithmeticInstances` derives each closed natural-input instance by
  induction, starting from `CT_Const` and using certified deterministic
  reductions. The smaller recursive call is typed by the induction hypothesis;
  the existing execution-correctness theorems are not used as typing premises.
- `NatArithmeticTyping.arithmetic_body_typing` classifies a world by the pair
  of input values. `nat_graph_joinable` proves that the precise natural result
  can be combined across these fibers, with all additional world variables
  retained.
- Lambda introduction and `CT_ArrowIntro` assemble the two arrows;
  `CT_PersistIntro` establishes the original persistent function specification.

The added general rules are `CT_Conv` (preserves both result sets and must
termination), `CT_ArrowIntro` (a value's applications must have actual typing
derivations), and `CT_FiberCases` (requires explicit fiber coverage and result
joinability). Their soundness lemmas are connected to `Fundamental` in
`ContextTyping.Soundness`; value-arrow soundness is proved in
`SoundnessArrowIntro`. Existing denotation and `CT_Fix` are unchanged.
No assumption of fiber stability for arbitrary arrows or persistent results
is introduced.

The declarative calculus now also has `CT_CtxCases`: a finite disjunctive
cover of contexts, with a typing derivation under every alternative and an
unchanged erased environment. Its soundness is proved by
`fundamental_ctx_cases_case` and included in `Fundamental`.
`ContextTyping.Subtyping` supplies reflexivity, transitivity, and intersection
projections without adding primitive typing rules.

The original `CT_Fix` has a mixed-world limitation.
`fix_rec_arg_impossible_at_min_zero` proves that a parent world with minimum
argument measure zero has no well-typed strictly smaller
recursive argument in any extension. This includes mixed worlds containing
both zero and positive inputs. Checking a recursive body after selecting its
positive-input stores therefore requires more than the new context-cover
rule: the recursive hypothesis must remain justified after that selection.
The arithmetic derivations above avoid that premise by using syntactic
induction on closed input instances and joining only precise base results.
They do not establish a general BST recursion or tree-coverage theorem.

The comparison with the paper's arrow and fixpoint definitions, including a
mixed-world analysis of Example 3.3 and the distinction between checked lemmas
and a mathematical countermodel, is recorded in
[SemanticsAudit.md](SemanticsAudit.md).

Build with the project's opam environment:

```bash
opam exec -- rocq makefile -f _CoqProject -o Makefile
opam exec -- make -j8
```
