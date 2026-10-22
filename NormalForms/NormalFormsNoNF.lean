import NormalForms.Basic

universe u

variable {α : Type u}

namespace Formula

def toNNF : Formula α → Formula α
  | var a           => var a
  | neg (var a)     => neg (var a)
  | neg (neg ψ)     => toNNF ψ
  | conj ψ χ        => conj (toNNF ψ) (toNNF χ)
  | disj ψ χ        => disj (toNNF ψ) (toNNF χ)
  | neg (conj ψ χ)  => disj (toNNF (neg ψ)) (toNNF (neg χ))
  | neg (disj ψ χ)  => conj (toNNF (neg ψ)) (toNNF (neg χ))

def distribDisj : Formula α → Formula α → Formula α
  | conj ψ χ, φ => conj (distribDisj ψ φ) (distribDisj χ φ)   -- (ψ ∧ χ) ∨ φ
  | φ, conj ψ χ => conj (distribDisj φ ψ) (distribDisj φ χ)   -- φ ∨ (ψ ∧ χ)
  | φ, ψ        => disj φ ψ

def NNFtoCNF : Formula α → Formula α
  | conj ψ χ => conj (NNFtoCNF ψ) (NNFtoCNF χ)
  | disj ψ χ => distribDisj (NNFtoCNF ψ) (NNFtoCNF χ)
  | φ        => φ   -- ik weet nog niet zeker wat hiermee te doen, mogelijk een voorwaarde?

def distribConj : Formula α → Formula α → Formula α
  | disj ψ χ, φ => disj (distribConj ψ φ) (distribConj χ φ)   -- (ψ ∧ χ) ∨ φ
  | φ, disj ψ χ => disj (distribConj φ ψ) (distribConj φ χ)   -- φ ∨ (ψ ∧ χ)
  | φ, ψ        => conj φ ψ

def NNFtoDNF : Formula α → Formula α
  | disj ψ χ => disj (NNFtoDNF ψ) (NNFtoDNF χ)
  | conj ψ χ => distribConj (NNFtoDNF ψ) (NNFtoDNF χ)
  | φ        => φ   -- ik weet nog niet zeker wat hiermee te doen, mogelijk een voorwaarde?

def toCNF (φ : Formula α) : Formula α :=
  NNFtoCNF (toNNF φ)

def toDNF (φ : Formula α) : Formula α :=
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

@[simp] lemma NNFtoCNF_var (a : α) : NNFtoCNF (var a) = var a := by simp [NNFtoCNF]
@[simp] lemma NNFtoCNF_neg (φ : Formula α) : NNFtoCNF (neg φ) = neg φ := by simp [NNFtoCNF]
@[simp] lemma NNFtoCNF_conj (ψ χ : Formula α) :
    NNFtoCNF (conj ψ χ) = conj (NNFtoCNF ψ) (NNFtoCNF χ) := by simp [NNFtoCNF]
@[simp] lemma NNFtoCNF_disj (ψ χ : Formula α) :
    NNFtoCNF (disj ψ χ) = distribDisj (NNFtoCNF ψ) (NNFtoCNF χ) := by simp [NNFtoCNF]

@[simp] lemma NNFtoDNF_var (a : α) : NNFtoDNF (var a) = var a := by simp [NNFtoDNF]
@[simp] lemma NNFtoDNF_neg (φ : Formula α) : NNFtoDNF (neg φ) = neg φ := by simp [NNFtoDNF]
@[simp] lemma NNFtoDNF_disj (ψ χ : Formula α) :
    NNFtoDNF (disj ψ χ) = disj (NNFtoDNF ψ) (NNFtoDNF χ) := by simp [NNFtoDNF]
@[simp] lemma NNFtoDNF_conj (ψ χ : Formula α) :
    NNFtoDNF (conj ψ χ) = distribConj (NNFtoDNF ψ) (NNFtoDNF χ) := by simp [NNFtoDNF]

@[simp] lemma toCNF_def (φ : Formula α) : toCNF φ = NNFtoCNF (toNNF φ) := rfl
@[simp] lemma toDNF_def (φ : Formula α) : toDNF φ = NNFtoDNF (toNNF φ) := rfl


end Formula
