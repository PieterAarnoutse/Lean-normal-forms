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
  | var a           => var a
  | neg (var a)     => neg (var a)
  | neg (neg ψ)     => toNNF ψ
  | conj ψ χ        => conj (toNNF ψ) (toNNF χ)
  | disj ψ χ        => disj (toNNF ψ) (toNNF χ)
  | neg (conj ψ χ)  => disj (toNNF (neg ψ)) (toNNF (neg χ))
  | neg (disj ψ χ)  => conj (toNNF (neg ψ)) (toNNF (neg χ))

def NNFtoCNF : Formula α → NF α
  | .var a    => [[Lit.pos a]]
  | .neg (.var a) => [[Lit.neg a]]
  | .conj φ ψ => NNFtoCNF φ ++ NNFtoCNF ψ
  | .disj φ ψ =>
      (NNFtoCNF φ).flatMap fun c₁ => (NNFtoCNF ψ).map fun c₂ => c₁ ++ c₂
  | _ => [[]] -- ik weet nog niet zeker wat hiermee te doen, mogelijk een voorwaarde?


def NNFtoDNF : Formula α → NF α
  | .var a    => [[Lit.pos a]]
  | .neg (.var a) => [[Lit.neg a]]
  | .disj φ ψ => NNFtoDNF φ ++ NNFtoDNF ψ
  | .conj φ ψ =>
      (NNFtoDNF φ).flatMap fun c₁ => (NNFtoDNF ψ).map fun c₂ => c₁ ++ c₂
  | _ => [[]] -- ik weet nog niet zeker wat hiermee te doen, mogelijk een voorwaarde?

def toCNF (φ : Formula α) : NF α :=
  NNFtoCNF (toNNF φ)

def toDNF (φ : Formula α) : NF α :=
  NNFtoDNF (toNNF φ)

  -- Lemmata

@[simp] lemma toNNF_var (a : α) : toNNF (var a) = var a := by simp [toNNF]
@[simp] lemma toNNF_neg (a : α) : toNNF (neg (var a)) = neg (var a) := by simp [toNNF]
@[simp] lemma toNNF_negneg (φ : Formula α) : toNNF (neg (neg φ)) = toNNF φ := by simp [toNNF]
@[simp] lemma toNNF_conj (ψ χ : Formula α) : toNNF (conj ψ χ) = conj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_disj (ψ χ : Formula α) : toNNF (disj ψ χ) = disj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_negconj (ψ χ : Formula α) : toNNF (neg (conj ψ χ)) =
  disj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF]
@[simp] lemma toNNF_negdisj (ψ χ : Formula α) : toNNF (neg (disj ψ χ)) =
  conj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF]

@[simp] lemma NNFtoCNF_var (a : α) : NNFtoCNF (var a) = [[Lit.pos a]] := rfl
@[simp] lemma NNFtoCNF_neg (a : α) : NNFtoCNF (neg (var a)) = [[Lit.neg a]] := rfl
@[simp] lemma NNFtoCNF_conj (φ ψ : Formula α) : NNFtoCNF (conj φ ψ) = NNFtoCNF φ ++ NNFtoCNF ψ
  := by simp [NNFtoCNF]
@[simp] lemma NNFtoCNF_disj (φ ψ : Formula α) : NNFtoCNF (disj φ ψ) =
  (NNFtoCNF φ).flatMap fun c₁ => (NNFtoCNF ψ).map fun c₂ => c₁ ++ c₂ := by simp [NNFtoCNF]

@[simp] lemma NNFtoDNF_var (a : α) : NNFtoDNF (var a) = [[Lit.pos a]] := rfl
@[simp] lemma NNFtoDNF_neg (a : α) : NNFtoDNF (neg (var a)) = [[Lit.neg a]] := rfl
@[simp] lemma NNFtoDNF_disj (φ ψ : Formula α) : NNFtoDNF (disj φ ψ) = NNFtoDNF φ ++ NNFtoDNF ψ
  := by simp [NNFtoDNF]
@[simp] lemma NNFtoDNF_conj (φ ψ : Formula α) : NNFtoDNF (conj φ ψ) =
  (NNFtoDNF φ).flatMap fun c₁ => (NNFtoDNF ψ).map fun c₂ => c₁ ++ c₂ := by simp [NNFtoDNF]

@[simp] lemma toCNF_def (φ : Formula α) : toCNF φ = NNFtoCNF (toNNF φ) := rfl
@[simp] lemma toDNF_def (φ : Formula α) : toDNF φ = NNFtoDNF (toNNF φ) := rfl

end Formula
