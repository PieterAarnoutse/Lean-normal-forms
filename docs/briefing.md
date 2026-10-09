# Internship brief

Build an efficient, usable Lean 4 library for propositional normal forms, with basic proofs. Start with the supplied code; keep atom names generic over a type `α`.

## Basic definitions

A formula is an atom, a negation `¬A`, a conjunction `A ∧ B` ("and"), or a disjunction `A ∨ B` ("or").

| Form | Definition | Example |
| --- | --- | --- |
| Literal | An atom or its negation | `p`, `¬q` |
| NNF (negation normal form) | A formula whose negations occur only directly before atoms | `p ∧ (¬q ∨ r)` |
| DNF (disjunctive normal form) | An "or" of groups of literals joined by "and" | `(p ∧ ¬q) ∨ r` |
| CNF (conjunctive normal form) | An "and" of groups of literals joined by "or" | `(p ∨ ¬q) ∧ r` |

Each group is a clause: conjunctive in DNF, disjunctive in CNF. Clauses and normal forms must be nonempty; single literals count. Specify bracketing.

There are no constants for "always true" or "always false". Joining a collection therefore needs an empty-input result (`Option`) or a nonemptiness proof.

## Keep syntax separate from meaning

Store formulas as written. Replacing `p ∧ p` by `p` requires a rule called idempotence. Changing order or brackets, removing `¬¬`, and distributing `∧` over `∨` also require rules.

Different applications permit different rules. Define the shapes independently and state which rules justify each conversion.

## Canonical and maximal forms

A canonical form chooses the same representative for any two formulas interchangeable under specified rules. Study these targets separately:

| Target | Definition and example |
| --- | --- |
| Fixed order and brackets | Choose, for example, `p ∧ (q ∧ r)` for reorderings/regroupings of these literals, if the rules permit those changes. Removing repetitions needs another rule. |
| Reduced forms | Remove redundant clauses using an explicit rule. Absorption, for example, permits reducing `p ∨ (p ∧ q)` to `p`, or `p ∧ (p ∨ q)` to `p`. |
| Full forms over `U` | Fix a finite atom set `U`. Every clause contains each atom in `U` exactly once, negated or unnegated. For `U = {p, q}`, `(p ∧ q) ∨ (p ∧ ¬q)` is a full DNF. Its clauses are called minterms; full CNF clauses are called maxterms. Fix clause order too. |
| Maximally consistent clauses over `U` | Choose a consistency condition. A consistent clause over `U` is maximal if adding any previously absent literal over `U` violates it. For "no atom occurs both negated and unnegated," `{p, ¬q}` is maximal over `{p, q}`, but `{p}` is not. |
| Closure under merging | Every merge of two clauses must already be present. For sets of literals, `{{p}, {q}}` needs the additional clause `{p, q}`. |

Being reduced, full or maximal does not by itself prove canonicality. Agree rules and targets with the supervisor.

## Checkpoints

- [ ] Build the project and run the [code guide's example](code.md).
- [ ] Agree representations that preserve order, brackets and repetitions by default.
- [ ] Define the normal-form types and conversions back to formulas. Prove that the resulting formulas have the promised shape.
- [ ] Implement conversions with explicit rule assumptions. Prove termination, preservation of occurring atoms, and that suitable conversions undo each other (round trips).
- [ ] Implement agreed canonical/maximal forms. Prove that normalizing twice equals normalizing once, and interchangeable inputs have equal canonical outputs.
- [ ] Read an assignment from a full conjunctive clause: `p ∧ ¬q` gives `p = true`, `q = false`. Specify treatment of absent atoms or both signs separately.
- [ ] Measure runtime, allocations and output size. Include `(p₁ ∨ q₁) ∧ ⋯ ∧ (pₙ ∨ qₙ)`, whose direct expansion has `2ⁿ` clauses when all atoms are distinct.

## First improvements

- [ ] Isolate the current finite-set representation (`Finset`): it loses order and repeated literals/clauses.
- [ ] Repair finite folds: `[a, b, c]` currently becomes `b ∧ (c ∧ a)`. Check disjunction and finite-set versions too.
- [ ] Add examples for empty collections, repeated literals, `p ∧ ¬p`, `p ∨ ¬p`, and round trips. Handle empty `U` and empty output explicitly.
- [ ] Profile clause combinations and sorting; compare lists/arrays with finite sets.
- [ ] Review `closedUnion` and the unused `dnfMeasure` (see the code guide). Correct stale comments and reduce duplicated proofs.

Each checkpoint should leave a buildable commit, examples and the rules used.
