# Internship brief

Build a usable, computationally efficient Lean 4 library for propositional normal forms, with basic proofs. Start with the supplied implementation. Keep atoms generic (`α`).

## Scope

The language is `φ ::= p | ¬φ | φ ∧ φ | φ ∨ φ`.

| Form | Shape |
| --- | --- |
| Literal | `p` or `¬p` |
| NNF | Literals joined by `∧` and `∨` |
| DNF | Nonempty disjunction of nonempty conjunctions of literals |
| CNF | Nonempty conjunction of nonempty disjunctions of literals |

Single literals count as all three normal forms. Specify bracketing. There are no `⊤` or `⊥` constants; empty folds must return `Option` or require a nonemptiness proof.

Definitions must preserve order, multiplicity and bracketing unless an explicit quotient identifies them. Reassociation, sorting, deduplication, distribution, absorption and negation rewrites each need stated laws when used to justify conversion. Keep syntactic equality separate from a client's equivalence relation.

Potential clients include classical logic, intuitionistic logic, K₃ (Strong Kleene), LP (Logic of Paradox), FDE (First Degree Entailment), truthmaker semantics and topic/hyperintensional semantics. No prior knowledge of these is required. The supervisor will supply the relevant laws and examples as needed.

Compatibility does not guarantee an equivalent NNF for every formula in every logic. For example, removing `¬¬p` is unavailable in intuitionistic logic; see [Sakharov on double-negation elimination](https://arxiv.org/abs/cs/0301026). State conversion correctness conditionally on the laws used.

## Checkpoints

- [ ] Build the project; evaluate examples containing repeated literals, complementary literals and nested negations.
- [ ] Audit the current representations. Propose a core that preserves syntax, with separate quotients for selected laws. Discuss the proposal before restructuring.
- [ ] Define normal-form predicates and datatypes, conversions to formulas, and a small construction API. Prove the represented formulas have the required shape.
- [ ] Specify each normalization algorithm and its required laws. Prove termination, variable preservation and applicable round trips; keep semantic correctness in separate client modules.
- [ ] Implement the canonical forms below. For each, state the equivalence relation, prove normalization is idempotent, and prove uniqueness where claimed.
- [ ] Add extension/enumeration operations over a fixed finite atom set `U`. Prove support, admissibility and maximality properties.
- [ ] Demonstrate valuation extraction from DNF clauses in a separate example. Treat positive and negative membership independently; state how missing atoms are handled. Start with classical logic, then K₃ or FDE with supervisor guidance.
- [ ] Benchmark runtime, allocations and output size; document one measured improvement. Include families with exponentially many output clauses.

## Canonical and maximal forms

| Target | Required specification |
| --- | --- |
| Structural representative | Fixed bracketing/order under explicitly chosen associativity/commutativity laws; remove duplicates only with idempotence. |
| Reduced DNF/CNF | Deterministic removal of subsumed clauses under absorption; state the exact relation for any uniqueness claim. |
| Merge closure | Close clause families under merging; distinguish this from consistency and maximality. |
| Full DNF/CNF over `U` | Classical minterms/maxterms contain exactly one polarity of every atom in `U`. Handle empty `U` and empty output explicitly. |
| Maximally consistent clauses | Fix a consistency predicate and literal universe over `U`; require consistency and no proper consistent extension within that universe. Distinguish this from a maximal consistent theory. |

For classical literal consistency, excluding complementary pairs gives exactly one polarity per atom at maximality. Other clients need different admissibility conditions: K₃ permits neither polarity, LP permits both, and FDE permits both or neither. These possibilities are explained in [Simonelli, §3](https://www.ryansimonelli.com/uploads/1/3/3/4/133499356/yes_no_neither_and_both__revised_for_synthese_01_.pdf). Membership records alone do not establish a completeness theorem.

## First improvements

- [ ] Replace or isolate the current `Finset` clauses: they discard order and repetitions at both levels.
- [ ] Repair `bigConj`/`bigDisj`: `[a, b, c]` currently becomes `b ⋆ (c ⋆ a)`. Check the nonempty finset variants too.
- [ ] Add executable examples for empty inputs, duplicate literals, `p ∧ ¬p`, `p ∨ ¬p`, and conversion round trips. Keep complementary literals unless a client justifies deletion.
- [ ] Profile Cartesian products, duplicate removal and sorting. Compare lists/arrays and shared subterms against the current implementation.
- [ ] Check `closedUnion` closure assumptions and the unused `dnfMeasure`. Correct stale comments; add missing dual CNF lemmas where useful.

Each checkpoint should leave a buildable commit, short examples and a note on the laws used. Agree priorities with the supervisor; full completeness proofs are later applications.
