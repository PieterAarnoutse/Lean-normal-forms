import NormalForms.Basic

universe u

variable {α : Type u}

-- Literals Type

inductive Lit (α : Type u) where
  | pos : α → Lit α
  | neg : α → Lit α

namespace Lit

def toFormula : Lit α → Formula α
  | .pos a => Formula.var a
  | .neg a => Formula.neg (.var a)

instance : Coe (Lit α) (Formula α) := ⟨toFormula⟩

def toStringAux [ToString α] : Lit α → String
  | .pos a => toString a
  | .neg a => "¬" ++ toString a

instance [ToString α] : ToString (Lit α) where
  toString φ := toStringAux φ

end Lit


namespace Formula


abbrev NF α := List (List (Lit α))

def toNNF : Formula α → Formula α
  | top             => top
  | bot             => bot
  | var a           => var a
  | neg (var a)     => neg (var a)
  | neg top         => bot
  | neg bot         => top
  | neg (neg ψ)     => toNNF ψ
  | conj ψ χ        => conj (toNNF ψ) (toNNF χ)
  | disj ψ χ        => disj (toNNF ψ) (toNNF χ)
  | neg (conj ψ χ)  => disj (toNNF (neg ψ)) (toNNF (neg χ))
  | neg (disj ψ χ)  => conj (toNNF (neg ψ)) (toNNF (neg χ))

def toCNF (φ : Formula α) : NF α :=
  NNFtoCNF (toNNF φ)
  where NNFtoCNF : Formula α → NF α
  | .top => []
  | .bot => [[]]
  | .var a    => [[Lit.pos a]]
  | .neg (.var a) => [[Lit.neg a]]
  | .conj φ ψ => NNFtoCNF φ ++ NNFtoCNF ψ
  | .disj φ ψ =>
      (NNFtoCNF φ).flatMap fun c₁ => (NNFtoCNF ψ).map fun c₂ => c₁ ++ c₂
      /-
      Explanation:
      The `flatMap` function is used to iterate over each clause `c₁` in the CNF of `φ`,
      and for each such clause, we iterate over each clause `c₂` in the CNF of `ψ`.
      We then concatenate these two clauses (`c₁ ++ c₂`)
      to form a new clause that represents the disjunction of the two original clauses.
      This effectively distributes the disjunction over the conjunctions,
      resulting in a CNF representation of the original formula.
      -/
  | _ => [[]]

def toDNF (φ : Formula α) : NF α :=
  NNFtoDNF (toNNF φ)
  where NNFtoDNF : Formula α → NF α
  | .top => [[]]
  | .bot => []
  | .var a    => [[Lit.pos a]]
  | .neg (.var a) => [[Lit.neg a]]
  | .disj φ ψ => NNFtoDNF φ ++ NNFtoDNF ψ
  | .conj φ ψ =>
      (NNFtoDNF φ).flatMap fun c₁ => (NNFtoDNF ψ).map fun c₂ => c₁ ++ c₂
      /-
      Explanation:
      The `flatMap` function is used to iterate over each clause `c₁` in the DNF of `φ`,
      and for each such clause, we iterate over each clause `c₂` in the DNF of `ψ`.
      We then concatenate these two clauses (`c₁ ++ c₂`)
      to form a new clause that represents the conjunction of the two original clauses.
      This effectively distributes the conjunction over the disjunctions,
      resulting in a DNF representation of the original formula.
      -/
  | _ => [[]]

  -- Lemmata

@[simp] lemma toNNF_var (a : α) : toNNF (var a) = var a := by simp [toNNF]
@[simp] lemma toNNF_neg (a : α) : toNNF (neg (var a)) = neg (var a) := by simp [toNNF]
@[simp] lemma toNNF_top : toNNF (top : Formula α) = top := by simp [toNNF]
@[simp] lemma toNNF_bot : toNNF (bot : Formula α) = bot := by simp [toNNF]
@[simp] lemma toNNF_neg_top : toNNF (neg (top : Formula α)) = bot := by simp [toNNF]
@[simp] lemma toNNF_neg_bot : toNNF (neg (bot : Formula α)) = top := by simp [toNNF]
@[simp] lemma toNNF_negneg (φ : Formula α) : toNNF (neg (neg φ)) = toNNF φ := by simp [toNNF]
@[simp] lemma toNNF_conj (ψ χ : Formula α) : toNNF (conj ψ χ) = conj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_disj (ψ χ : Formula α) : toNNF (disj ψ χ) = disj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_negconj (ψ χ : Formula α) : toNNF (neg (conj ψ χ)) =
  disj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF]
@[simp] lemma toNNF_negdisj (ψ χ : Formula α) : toNNF (neg (disj ψ χ)) =
  conj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF]

/-
@[simp] lemma toCNF_def (φ : Formula α) : toCNF φ = NNFtoCNF (toNNF φ) := rfl
@[simp] lemma toDNF_def (φ : Formula α) : toDNF φ = NNFtoDNF (toNNF φ) := rfl
-/

-- toFormula

/-- Converts a CNF to a formula. -/
def CNFtoFormula (CNF : NF α) : Formula α :=
  bigConj (CNF.map fun clause => bigDisj (clause.map Lit.toFormula))
  /-
  Explanation:
  The `bigConj` function is used to combine all the clauses in the CNF into a single conjunction.
  Each clause is represented as a list of literals,
  and `bigDisj` is used to combine the literals within each clause into a disjunction.
  -/

/-- Converts a DNF to a formula. -/
def DNFtoFormula (DNF : NF α) : Formula α :=
  bigDisj (DNF.map fun clause => bigConj (clause.map Lit.toFormula))
  /-
  Explanation:
  The `bigDisj` function is used to combine all the clauses in the DNF into a single disjunction.
  Each clause is represented as a list of literals,
  and `bigConj` is used to combine the literals within each clause into a conjunction.
  -/


@[simp] lemma CNFtoFormula_def : (CNF : NF α) → CNFtoFormula CNF = bigConj (CNF.map fun clause
  => bigDisj (clause.map Lit.toFormula)) := by simp [CNFtoFormula]
@[simp] lemma DNFtoFormula_def : (DNF : NF α) → DNFtoFormula DNF = bigDisj (DNF.map fun clause
  => bigConj (clause.map Lit.toFormula)) := by simp [DNFtoFormula]
@[simp] lemma CNFtoFormula_nil : CNFtoFormula ([] : NF α) = top := by simp [CNFtoFormula]
@[simp] lemma DNFtoFormula_nil : DNFtoFormula ([] : NF α) = bot := by simp [DNFtoFormula]


end Formula
