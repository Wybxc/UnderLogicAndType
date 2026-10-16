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
| `DisproveMerge` | List membership/sortedness predicates and merge safety/disproof types |

The imported definitions retain their original names and bodies, except for
`BSTGenerator`: its specification now describes a persistent function taking
`r`, `lo`, and a persistent range function. The range contract has an
over-approximate domain `x < y` and an under-approximate result `x < ν < y`.
The generator has an under-approximate tree result satisfying the BST
predicate and `tree_mem n t <-> lo < n <= lo + r`. Its result qualifier uses
`arg2` for `r` and `arg1` for `lo`; the nearest argument is the range function.
The existing BST convention permits duplicates in right subtrees.

Programs, typing
derivations, semantic-subtyping proof obligations, and the binary-operation
result qualifiers used by those obligations are omitted. The shared
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

`ContextTyping/theories/Typing.v` and its context-type rules are unchanged.
The source branch's `ExtendedTyping`, `ExtendedSubsumption`, inference
automation, and binary-operation language extension are not imported.

Build with the project's opam environment:

```bash
opam exec -- rocq makefile -f _CoqProject -o Makefile
opam exec -- make -j8
```
