import NormalForms.NormalForms_tussentype
set_option linter.style.longLine false

universe u v

variable {α : Type u}

namespace Formula

private def deduplicateAdjacentByFormula [DecidableEq α] {β : Type v}
    (toFormula : β → Formula α) (xs : List β) : List β :=
  xs.foldl (fun acc x =>
    if acc.getLast?.any (fun last => decide (toFormula last = toFormula x)) then acc
    else acc ++ [x]) []

private def conjArgs : Formula α → List (Formula α)
  | .conj φ ψ => conjArgs φ ++ conjArgs ψ
  | φ => [φ]

private def disjArgs : Formula α → List (Formula α)
  | .disj φ ψ => disjArgs φ ++ disjArgs ψ
  | φ => [φ]

private def dcArgs : DC α → List (DC α)
  | .disj φ ψ => dcArgs φ ++ dcArgs ψ
  | dc => [dc]

private def ccArgs : CC α → List (CC α)
  | .conj φ ψ => ccArgs φ ++ ccArgs ψ
  | cc => [cc]

private def cnfArgs : CNF α → List (CNF α)
  | .conj φ ψ => cnfArgs φ ++ cnfArgs ψ
  | cnf => [cnf]

private def dnfArgs : DNF α → List (DNF α)
  | .disj φ ψ => dnfArgs φ ++ dnfArgs ψ
  | dnf => [dnf]

private def rebuildFormulaConj (fallback : Formula α) : List (Formula α) → Formula α
  | [] => fallback
  | x :: xs => xs.foldl Formula.conj x

private def rebuildFormulaDisj (fallback : Formula α) : List (Formula α) → Formula α
  | [] => fallback
  | x :: xs => xs.foldl Formula.disj x

private def rebuildDC (fallback : DC α) : List (DC α) → DC α
  | [] => fallback
  | x :: xs => xs.foldl DC.disj x

private def rebuildCC (fallback : CC α) : List (CC α) → CC α
  | [] => fallback
  | x :: xs => xs.foldl CC.conj x

private def rebuildCNF (fallback : CNF α) : List (CNF α) → CNF α
  | [] => fallback
  | x :: xs => xs.foldl CNF.conj x

private def rebuildDNF (fallback : DNF α) : List (DNF α) → DNF α
  | [] => fallback
  | x :: xs => xs.foldl DNF.disj x

private def idpotRedFormula [DecidableEq α] : Formula α → Formula α
  | .var a => .var a
  | .neg φ => .neg (idpotRedFormula φ)
  | .conj φ ψ =>
      let φ' := idpotRedFormula φ
      let ψ' := idpotRedFormula ψ
      let terms := deduplicateAdjacentByFormula id (conjArgs (.conj φ' ψ'))
      rebuildFormulaConj (.conj φ' ψ') terms
  | .disj φ ψ =>
      let φ' := idpotRedFormula φ
      let ψ' := idpotRedFormula ψ
      let terms := deduplicateAdjacentByFormula id (disjArgs (.disj φ' ψ'))
      rebuildFormulaDisj (.disj φ' ψ') terms
  | .imp φ ψ => .imp (idpotRedFormula φ) (idpotRedFormula ψ)
  | .iff φ ψ => .iff (idpotRedFormula φ) (idpotRedFormula ψ)

private def idpotRedDC [DecidableEq α] : DC α → DC α
  | .lit lit => .lit lit
  | .disj φ ψ =>
      let φ' := idpotRedDC φ
      let ψ' := idpotRedDC ψ
      let terms := deduplicateAdjacentByFormula DC.toFormula (dcArgs (.disj φ' ψ'))
      rebuildDC (.disj φ' ψ') terms

private def idpotRedCC [DecidableEq α] : CC α → CC α
  | .lit lit => .lit lit
  | .conj φ ψ =>
      let φ' := idpotRedCC φ
      let ψ' := idpotRedCC ψ
      let terms := deduplicateAdjacentByFormula CC.toFormula (ccArgs (.conj φ' ψ'))
      rebuildCC (.conj φ' ψ') terms

private def idpotRedCNF [DecidableEq α] : CNF α → CNF α
  | .disjclause dc => .disjclause (idpotRedDC dc)
  | .conj φ ψ =>
      let φ' := idpotRedCNF φ
      let ψ' := idpotRedCNF ψ
      let terms := deduplicateAdjacentByFormula CNF.toFormula (cnfArgs (.conj φ' ψ'))
      rebuildCNF (.conj φ' ψ') terms

private def idpotRedDNF [DecidableEq α] : DNF α → DNF α
  | .conjclause cc => .conjclause (idpotRedCC cc)
  | .disj φ ψ =>
      let φ' := idpotRedDNF φ
      let ψ' := idpotRedDNF ψ
      let terms := deduplicateAdjacentByFormula DNF.toFormula (dnfArgs (.disj φ' ψ'))
      rebuildDNF (.disj φ' ψ') terms

class IdpotReduces (β : Type v) where
  reduce : β → β

instance [DecidableEq α] : IdpotReduces (Formula α) where
  reduce := idpotRedFormula

instance [DecidableEq α] : IdpotReduces (CNF α) where
  reduce := idpotRedCNF

instance [DecidableEq α] : IdpotReduces (DNF α) where
  reduce := idpotRedDNF

/-- Remove consecutive repeated terms from associative conjunctions/disjunctions, preserving input type. -/
def idpotRed {β : Type v} [reducer : IdpotReduces β] (φ : β) : β :=
  reducer.reduce φ

private def sortByFormula [Ord α] {β : Type v}
    (toFormula : β → Formula α) (xs : List β) : List β :=
  xs.mergeSort (fun a b => compare (toFormula a) (toFormula b) != Ordering.gt)

private def idcomRedFormula [Ord α] [DecidableEq α] : Formula α → Formula α
  | .var a => .var a
  | .neg φ => .neg (idcomRedFormula φ)
  | .conj φ ψ =>
      let φ' := idcomRedFormula φ
      let ψ' := idcomRedFormula ψ
      let xs := sortByFormula id (conjArgs (.conj φ' ψ'))
      rebuildFormulaConj (.conj φ' ψ') xs
  | .disj φ ψ =>
      let φ' := idcomRedFormula φ
      let ψ' := idcomRedFormula ψ
      let xs := sortByFormula id (disjArgs (.disj φ' ψ'))
      rebuildFormulaDisj (.disj φ' ψ') xs
  | .imp φ ψ => .imp (idcomRedFormula φ) (idcomRedFormula ψ)
  | .iff φ ψ => .iff (idcomRedFormula φ) (idcomRedFormula ψ)

private def idcomRedDC [Ord α] [DecidableEq α] (dc : DC α) : DC α :=
  let xs := sortByFormula DC.toFormula (dcArgs dc)
  rebuildDC dc xs

private def idcomRedCC [Ord α] [DecidableEq α] (cc : CC α) : CC α :=
  let xs := sortByFormula CC.toFormula (ccArgs cc)
  rebuildCC cc xs

private def idcomRedCNF [Ord α] [DecidableEq α] : CNF α → CNF α
  | .disjclause dc => .disjclause (idcomRedDC dc)
  | .conj φ ψ =>
      let φ' := idcomRedCNF φ
      let ψ' := idcomRedCNF ψ
      let xs := sortByFormula CNF.toFormula (cnfArgs (.conj φ' ψ'))
      rebuildCNF (.conj φ' ψ') xs

private def idcomRedDNF [Ord α] [DecidableEq α] : DNF α → DNF α
  | .conjclause cc => .conjclause (idcomRedCC cc)
  | .disj φ ψ =>
      let φ' := idcomRedDNF φ
      let ψ' := idcomRedDNF ψ
      let xs := sortByFormula DNF.toFormula (dnfArgs (.disj φ' ψ'))
      rebuildDNF (.disj φ' ψ') xs

class IdcomReduces (β : Type v) where
  reduce : β → β

instance [Ord α] [DecidableEq α] : IdcomReduces (Formula α) where
  reduce := idcomRedFormula

instance [Ord α] [DecidableEq α] : IdcomReduces (CNF α) where
  reduce := idcomRedCNF

instance [Ord α] [DecidableEq α] : IdcomReduces (DNF α) where
  reduce := idcomRedDNF

/-- Normalize under idempotence and commutativity, preserving the input syntax type. -/
def idcomRed {β : Type v} [reducer : IdcomReduces β] (φ : β) : β :=
  reducer.reduce φ

private def clauseContainsAtom [DecidableEq α] : CC α → α → Bool
  | .lit (.pos a), x => decide (a = x)
  | .lit (.neg a), x => decide (a = x)
  | .conj φ ψ, x => clauseContainsAtom φ x || clauseContainsAtom ψ x

private def completeClause [DecidableEq α] (atoms : List α) (cc : CC α) : CC α :=
  atoms.foldl (fun acc a =>
    if clauseContainsAtom acc a then acc else .conj acc (.lit (.pos a))) cc

private def completeDNF [DecidableEq α] (atoms : List α) : DNF α → DNF α
  | .conjclause cc => .conjclause (completeClause atoms cc)
  | .disj φ ψ => .disj (completeDNF atoms φ) (completeDNF atoms ψ)

private def clauseContainsAtomDC [DecidableEq α] : DC α → α → Bool
  | .lit (.pos a), x => decide (a = x)
  | .lit (.neg a), x => decide (a = x)
  | .disj φ ψ, x => clauseContainsAtomDC φ x || clauseContainsAtomDC ψ x

private def completeDC [DecidableEq α] (atoms : List α) (dc : DC α) : DC α :=
  atoms.foldl (fun acc a =>
    if clauseContainsAtomDC acc a then acc else .disj acc (.lit (.pos a))) dc

private def completeCNF [DecidableEq α] (atoms : List α) : CNF α → CNF α
  | .disjclause dc => .disjclause (completeDC atoms dc)
  | .conj φ ψ => .conj (completeCNF atoms φ) (completeCNF atoms ψ)

private def formulaAtoms [Ord α] [DecidableEq α] (φ : Formula α) : List α :=
  let sorted := (varsList φ).mergeSort (fun a b => compare a b != Ordering.gt)
  deduplicateAdjacentByFormula Formula.var sorted

private def dnfAtoms [Ord α] [DecidableEq α] (φ : DNF α) : List α :=
  formulaAtoms (DNF.toFormula φ)

private def cnfAtoms [Ord α] [DecidableEq α] (φ : CNF α) : List α :=
  formulaAtoms (CNF.toFormula φ)

/-- Maximal-form conversions preserve normal-form inputs; formulas are converted to DNF. -/
class MaxForm (Input : Type v) (Output : outParam (Type v)) where
  apply : Input → Output

instance [Ord α] [DecidableEq α] : MaxForm (Formula α) (DNF α) where
  apply φ := completeDNF (formulaAtoms φ) (Formula.toDNF φ)

instance [Ord α] [DecidableEq α] : MaxForm (DNF α) (DNF α) where
  apply φ := completeDNF (dnfAtoms φ) φ

instance [Ord α] [DecidableEq α] : MaxForm (CNF α) (CNF α) where
  apply φ := completeCNF (cnfAtoms φ) φ

/-- Complete clauses over the atoms already present; a `Formula` input is first converted to DNF. -/
def maxForm {Input : Type v} {Output : Type v}
    [operation : MaxForm Input Output] (φ : Input) : Output :=
  operation.apply φ

end Formula
