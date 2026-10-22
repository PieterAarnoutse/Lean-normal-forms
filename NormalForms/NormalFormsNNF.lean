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


-- NNF Type

inductive NNF (α : Type u) where
  | lit : Lit α → NNF α
  | conj : NNF α → NNF α → NNF α
  | disj : NNF α → NNF α → NNF α

namespace NNF

def toStringAux [ToString α] : NNF α → String
  | .lit a    =>  toString a
  | .conj φ ψ => "(" ++ toStringAux φ ++ " ∧ " ++ toStringAux ψ ++ ")"
  | .disj φ ψ => "(" ++ toStringAux φ ++ " ∨ " ++ toStringAux ψ ++ ")"

instance [ToString α] : ToString (NNF α) where
  toString φ := toStringAux φ

abbrev NF α := List (List (Lit α))

def toCNF : NNF α → NF α
  | .lit a    => [[a]]
  | .conj φ ψ => toCNF φ ++ toCNF ψ
  | .disj φ ψ =>
      (toCNF φ).flatMap fun c₁ => (toCNF ψ).map fun c₂ => c₁ ++ c₂

def toDNF : NNF α → NF α
  | .lit a    => [[a]]
  | .disj φ ψ => toDNF φ ++ toDNF ψ
  | .conj φ ψ =>
      (toDNF φ).flatMap fun c₁ => (toDNF ψ).map fun c₂ => c₁ ++ c₂

  -- Lemmata
@[simp] lemma toCNF_lit (a : Lit α) : toCNF (NNF.lit a) = [[a]] := rfl
@[simp] lemma toCNF_conj (φ ψ : NNF α) : toCNF (.conj φ ψ) = toCNF φ ++ toCNF ψ := by
  simp [toCNF]
@[simp] lemma toCNF_disj (φ ψ : NNF α) :
    toCNF (.disj φ ψ) = (toCNF φ).flatMap fun c₁ => (toCNF ψ).map fun c₂ => c₁ ++ c₂ := by
  simp [toCNF]

@[simp] lemma toDNF_lit (a : Lit α) : toDNF (NNF.lit a) = [[a]] := rfl
@[simp] lemma toDNF_disj (φ ψ : NNF α) : toDNF (.disj φ ψ) = toDNF φ ++ toDNF ψ := by
  simp [toDNF]
@[simp] lemma toDNF_conj (φ ψ : NNF α) :
    toDNF (.conj φ ψ) = (toDNF φ).flatMap fun c₁ => (toDNF ψ).map fun c₂ => c₁ ++ c₂ := by
  simp [toDNF]

end NNF

-- Functions

namespace Formula

abbrev NF α := List (List (Lit α))

def toNNF : Formula α → NNF α
  | var a           => NNF.lit (Lit.pos a)
  | neg (var a)     => NNF.lit (Lit.neg a)
  | neg (neg ψ)     => toNNF ψ
  | conj ψ χ        => NNF.conj (toNNF ψ) (toNNF χ)
  | disj ψ χ        => NNF.disj (toNNF ψ) (toNNF χ)
  | neg (conj ψ χ)  => NNF.disj (toNNF (neg ψ)) (toNNF (neg χ))
  | neg (disj ψ χ)  => NNF.conj (toNNF (neg ψ)) (toNNF (neg χ))

def toCNF (φ : Formula α) : NF α :=
  NNF.toCNF (toNNF φ)

def toDNF (φ : Formula α) : NF α :=
  NNF.toDNF (toNNF φ)

  -- Lemmata

@[simp] lemma toNNF_var (a : α) : toNNF (var a) = NNF.lit (Lit.pos a) := by simp [toNNF]
@[simp] lemma toNNF_neg (a : α) : toNNF (neg (var a)) = NNF.lit (Lit.neg a) := by simp [toNNF]
@[simp] lemma toNNF_negneg (φ : Formula α) : toNNF (neg (neg φ)) = toNNF φ := by simp [toNNF]
@[simp] lemma toNNF_conj (ψ χ : Formula α) : toNNF (conj ψ χ) = NNF.conj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_disj (ψ χ : Formula α) : toNNF (disj ψ χ) = NNF.disj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_negconj (ψ χ : Formula α) : toNNF (neg (conj ψ χ)) =
  NNF.disj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF]
@[simp] lemma toNNF_negdisj (ψ χ : Formula α) : toNNF (neg (disj ψ χ)) =
  NNF.conj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF]

@[simp] lemma toCNF_def (φ : Formula α) : toCNF φ = NNF.toCNF (toNNF φ) := rfl
@[simp] lemma toDNF_def (φ : Formula α) : toDNF φ = NNF.toDNF (toNNF φ) := rfl


end Formula
