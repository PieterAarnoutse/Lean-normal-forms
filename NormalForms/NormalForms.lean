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

def toCNF : NNF α → List (List (Lit α))
  | .lit a    => [[a]]
  | .conj φ ψ => toCNF φ ++ toCNF ψ
  | .disj φ ψ =>
      (toCNF φ).flatMap fun c₁ => (toCNF ψ).map fun c₂ => c₁ ++ c₂

def toDNF : NNF α → List (List (Lit α))
  | .lit a    => [[a]]
  | .disj φ ψ => toDNF φ ++ toDNF ψ
  | .conj φ ψ =>
      (toDNF φ).flatMap fun c₁ => (toDNF ψ).map fun c₂ => c₁ ++ c₂

end NNF

-- Functions

namespace Formula

def toNNF : Formula α → NNF α
  | var a           => NNF.lit (Lit.pos a)
  | neg (var a)     => NNF.lit (Lit.neg a)
  | neg (neg ψ)     => toNNF ψ
  | conj ψ χ        => NNF.conj (toNNF ψ) (toNNF χ)
  | disj ψ χ        => NNF.disj (toNNF ψ) (toNNF χ)
  | neg (conj ψ χ)  => NNF.disj (toNNF (neg ψ)) (toNNF (neg χ))
  | neg (disj ψ χ)  => NNF.conj (toNNF (neg ψ)) (toNNF (neg χ))

end Formula
