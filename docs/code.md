# Code guide

The normal-form definitions and converters are short. Most of the file supplies proofs, ordering, printing and conversions between types. Combining clauses, for example, needs both a function and proofs about nonemptiness and literal membership.

## Build and files

Lean and Mathlib are pinned to `v4.29.0-rc4`. From the repository root:

```sh
lake exe cache get
lake build
```

Import `NormalForms`. Most names live in the `Formula` namespace.

| Module | Purpose |
| --- | --- |
| [NormalForms.lean](../NormalForms.lean) | Imports the library for users. |
| [Basic.lean](../NormalForms/Basic.lean) | Defines formula trees and general operations on them. |
| [NormalForms/NormalForms.lean](../NormalForms/NormalForms.lean) | Defines normal-form representations, conversions and proofs. |

## Read the definitions first

Read `NormalForms/NormalForms.lean` in this order, initially skipping proof bodies:

| Start at | What it contributes |
| --- | --- |
| `Literal` (line 24) | `pos p` and `neg p` encode `p` and `¬p`. `compl` flips the sign. |
| `NNF` (840) | A tree built from literals using only `conj` and `disj`. |
| `ConjunctiveClause`, `DisjunctiveClause` (122) | A nonempty finite set of literals, joined by `∧` or `∨`. Separate types prevent mixing the roles. |
| `DisjunctiveNormalForm`, `ConjunctiveNormalForm` (455) | Nonempty finite sets of the appropriate clause type. `DNF` and `CNF` are abbreviations. |
| `NNF.dnf`, `NNF.cnf` (960) | Recursively convert an NNF into a collection of clauses. |
| `nnfAux`, `Formula.nnf` (1094) | Push negations to atoms; a Boolean flag records whether to negate the current subtree. |

The types enforce the shape: a `Formula` can contain `¬(p ∧ q)`; an `NNF` cannot. Nonemptiness proofs rule out empty clauses and normal forms.

## Literals as a type or a predicate

The current `Literal α` stores a sign and an atom. An alternative is to recognize literals among existing formulas:

```lean
universe u

def IsLiteral {α : Type u} : Formula α → Prop
  | .var _ => True
  | .neg (.var _) => True
  | _ => False
```

Thus `IsLiteral (¬p)` holds, while `IsLiteral (¬¬p)` does not. The corresponding set is `{φ : Formula α | IsLiteral φ}`. Mathlib's [Set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html#Set) describes membership through a predicate; this does not enumerate the literals. For executable filtering, also supply a decision procedure (`DecidablePred IsLiteral`).

| Representation | Advantages | Costs |
| --- | --- | --- |
| `Literal α` | Every value is a literal. Functions such as `compl` have exactly two cases. Stores the sign and atom directly. | Needs conversion to `Formula` and lemmas connecting the two types. Converting an arbitrary formula back can fail. |
| `IsLiteral : Formula α → Prop` | Reuses formula operations and lemmas. Statements about literals can stay within the formula type. | A function needs both a formula and evidence that it is a literal. Operations must prove they preserve the property; matching a formula still exposes all its constructors. |

A [subtype](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Subtype.html), `{φ : Formula α // IsLiteral φ}`, packages the formula with that evidence. It can be the element type of a clause, just as `Literal α` is now. Its proofs are erased during compilation, so carrying proofs does not itself make it slower; compare the stored data and conversion costs. See the [Lean reference on subtypes](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/).

Both views can coexist, with conversion lemmas connecting them. The same choice arises for NNF, CNF and DNF.

## Follow one conversion

`p ∧ (q ∨ ¬r)` is already in NNF. DNF conversion proceeds as follows; braces denote sets:

```text
p           -> {{p}}
q ∨ ¬r      -> {{q}, {¬r}}
p ∧ (q ∨ ¬r) -> {{p, q}, {p, ¬r}}
```

The three cases of `NNF.dnf` are:

1. A literal becomes a single clause containing that literal (`singleton` at both levels).
2. A disjunction combines the two collections of clauses (`union`).
3. A conjunction merges every pair of clauses, one from each collection (`distributeConj`, using [Finset.image₂](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/NAry.html#Finset.image%E2%82%82)).

`NNF.cnf` uses union for conjunction and pairwise merging for disjunction. `Formula.dnf`/`cnf` first call `nnf`; `toFormula` rebuilds formula trees. The `*ToFormula` wrappers combine these steps.

Finite sets forget order and repetitions: `{p, p}` is already `{p}`. Preserving occurrences requires a different representation.

## Orderings

A set such as `{p, q}` has no first element. Rebuilding a formula requires choosing between trees such as `p ∧ q` and `q ∧ p`. [Finset.sort](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Sort.html#Finset.sort) produces a list in a fixed order; the finite folds then build the tree. Sorting also makes printed collections reproducible. This convention does not establish that reordered formulas have the same meaning.

The code obtains its orders in three steps:

1. `orderCode` encodes formulas as lists of constructor tags and atoms. It compares these lexicographically: the first differing token decides, as in dictionary order. A decoder proves that distinct formulas have distinct codes. [LinearOrder.lift'](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Basic.html#LinearOrder.lift') then transfers the list order to formulas.
2. Literals inherit the formula order through `toFormula`.
3. Clauses are compared by their sorted literal lists. The `sorted_injective` proofs establish that this comparison distinguishes clauses.

Clause and CNF/DNF `toFormula` functions sort the converted formulas before folding. Comparisons may rebuild token lists or sorted lists; these are costs to profile.

`[DecidableEq α]` provides an equality test for atom names, enough for clause merging and CNF/DNF computation. `[LinearOrder α]` also provides comparisons for sorting and reconstruction; `[ToString α]` provides printing. A list-based representation can preserve its input order without requiring an atom order.

Mathlib's [list lexicographic order](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Lex.html) explains the comparison. [Finset.mem_sort](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Sort.html#Finset.mem_sort) and [Finset.sort_toFinset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Sort.html#Finset.sort_toFinset) state that sorting preserves membership and recovers the original set.

## What the proofs and helper code do

| Code | Why it is present |
| --- | --- |
| Nonemptiness proofs | A merged clause must still contain a literal; either input supplies one. |
| `mem_merge` | Proves that membership in a merged clause means membership in at least one input. Later proofs reuse this fact. |
| `@[simp]` lemmas | Teach Lean's simplifier equations, e.g. flipping a literal's sign twice returns the original. |
| `@[ext]` lemmas | Reduce clause equality to equality of stored sets, without comparing nonemptiness proofs. |
| `Coe` instances | Insert conversions automatically, e.g. from a literal to a formula. Supporting lemmas let `simp` work through them. |
| Ordering and printing instances | Provide sorted output, readable `#eval` results, and an order for rebuilding formula trees. |
| Complement lemmas | Relate CNF and DNF when literal signs and `∧`/`∨` are exchanged. |

Separate CNF/DNF implementations repeat definitions and proofs. Reducing this duplication and separating optional code are possible improvements.

`nnf_neg_neg` proves that `¬¬A` and `A` produce the same NNF output. Whether they mean the same thing requires a separate correctness theorem with assumptions about negation.

## Supporting and optional code

In `Basic.lean`, `varsList` and `subformulaList` collect occurrences; `vars` and `subformulas` remove duplicates. `subst` replaces an atom by a formula. `complexity` measures tree height and supports induction.

`bigConj`/`bigDisj` join lists and return `none` for empty inputs; the `FinsetNE` variants require nonemptiness proofs. Their current fold puts the first element last: `[a, b, c]` becomes `b ∧ (c ∧ a)`. This needs repair.

The optional `closedDnf` adds merged clauses: for `p ∨ q`, it includes `{p, q}` alongside `{p}` and `{q}`. `closedCnf` does the corresponding construction. `closedUnion` adds merges between its two inputs; full closure may require further merges.

`size`, `disjCount`, `dnfDebt` and `dnfMeasure` measure tree structure. Conversion terminates by recursion on smaller subtrees; these measures are unused.

The module header is stale: clauses and normal forms are structures, and their `toFormula` functions return formulas directly. Canonical forms, consistency/maximality tests and assignment extraction are still project work.

## Run an example

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
