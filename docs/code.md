# Code guide

## Build and entry point

Lean and Mathlib are pinned to `v4.29.0-rc4`; `lake-manifest.json` pins dependency commits. With Lean installed, run from the repository root:

```sh
lake exe cache get
lake build
```

Import `NormalForms` in client files. Both source files were copied from the supplied directory; only the local import path changed. The namespace remains `Formula`.

| Module | Contents |
| --- | --- |
| [NormalForms.lean](../NormalForms.lean) | Public import |
| [NormalForms/Basic.lean](../NormalForms/Basic.lean) | Formula trees, traversal, substitution, ordering and finite folds |
| [NormalForms/NormalForms.lean](../NormalForms/NormalForms.lean) | Literals, clauses, NNF, CNF, DNF, conversions and structural lemmas |

## Basic syntax

`Formula α` is a binary tree with constructors `var`, `neg`, `conj`, `disj`. Equality compares trees. It preserves repeated occurrences, order and bracketing.

| API | Behavior |
| --- | --- |
| `varsList`, `subformulaList` | Traverse occurrences, preserving repetitions; a formula is its own subformula. |
| `vars`, `subformulas` | Convert occurrence lists to finite sets. |
| `complexity` | Tree height: atoms have height zero; binary nodes use `max + 1`. |
| `inductionOnComplexity` | Induction using smaller height; justified by `wf_ltComplexity`. |
| `subst φ i θ` | Replace every occurrence of atom `i` by formula `θ`. |
| `orderCode` | Prefix token encoding; an internal decoder proves injectivity. Lexicographic comparison supplies a formula order. |
| `sorted` | Sort a finite set by that structural order. |
| `bigConj`, `bigDisj` | Fold lists, returning `none` on `[]`. |
| `bigConjFinset`, `bigDisjFinset` | Sort a finite set, then use the list fold. |
| `bigConjFinsetNE`, `bigDisjFinsetNE` | Produce a formula using a proof that the finite set is nonempty. |

Current fold order: `bigConj [a, b, c] = some (b ∧ (c ∧ a))`. The head is the fold seed. The nonempty finset variants put the minimum last in the same way. Output is deterministic, but its traversal order differs from the documented sorted order.

## Normal-form data

`Literal α` has constructors `pos a` and `neg a`. `atom` forgets the sign; `compl` flips it; `toFormula` embeds the literal. Complementation is involutive.

`NNF α` is a tree of `lit`, `conj`, `disj`. Its shape restricts negation to literals. `NNF.compl` flips signs and exchanges conjunction/disjunction. `size` counts nodes; `disjCount` counts disjunctions. `dnfDebt` counts disjunctions under conjunction ancestors, and `dnfMeasure = size + dnfDebt`. The converters use structural recursion, not this measure; its decrease under distributive rewriting is unproved.

`ConjunctiveClause` and `DisjunctiveClause` contain a `Finset (Literal α)` plus a nonemptiness proof. `DNF` contains a nonempty finite set of conjunctive clauses; `CNF` contains a nonempty finite set of disjunctive clauses. These are structures, despite the module header calling them type synonyms. Their `toFormula` functions are total; the header's `Option` description is stale.

Finite sets identify permutations and duplicates. `merge` is set union, so `merge C C = C`. Clauses may contain both polarities of an atom. There is no consistency check or general absorption pass.

## Conversion pipeline

```text
Formula α ── nnf ──> NNF α ── NNF.dnf / NNF.cnf ──> DNF α / CNF α
    ^                    |                                  |
    └──── toFormula ──────┴────────── toFormula ──────────────┘
```

- `nnfAux` carries a negation flag. Negation flips it; a negative flag swaps `conj`/`disj` and negates literals. `Formula.nnf` starts with the flag off.
- `NNF.dnf` turns disjunction into clause union and conjunction into a Cartesian product of clause merges (`distributeConj`). `NNF.cnf` is dual, using `distributeDisj`.
- `Formula.dnf` and `Formula.cnf` compose those operations with `nnf`. The `*ToFormula` wrappers rebuild ordinary formula trees.
- `closedUnion` adds the two input families and their cross-merges. `closedDnf`/`closedCnf` use this operation at the corresponding union step. A single `closedUnion` is not a general closure procedure for arbitrary inputs; closure requires hypotheses on its inputs.

`nnf` needs no atom instances. Set operations generally require `[DecidableEq α]`; sorting and clause/DNF/CNF conversion to formulas require `[LinearOrder α]`. Printing also needs `[ToString α]`.

## Existing results and limits

The code proves constructor equations, membership/extensionality lemmas, complement involutions, DNF distribution identities, NNF embedding round trips, complement/CNF/DNF duality, and inclusion of ordinary DNF clauses in `closedDnf`.

These are equalities of the chosen data structures. No theorem connects conversion to an arbitrary semantics. In particular, `nnf_neg_neg` states equality of conversion outputs; it does not establish `¬¬φ = φ` or a logic's equivalence between those formulas. Canonicality under a specified logic, consistency, maximality, valuation extraction and semantic correctness remain to be developed.

## Small example

Save this as `Example.lean` at the repository root and run `lake env lean Example.lean`:

```lean
import NormalForms

def sample : Formula Nat :=
  .conj (.var 0) (.disj (.var 1) (.neg (.var 2)))

#eval sample.nnf
#eval sample.dnf.clauses.card  -- 2
#eval sample.cnf.clauses.card  -- 2

example (a : Nat) :
    Formula.nnf (.neg (.neg (.var a))) = Formula.nnf (.var a) := rfl
```
