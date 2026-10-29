import NormalForms.Basic

universe u

variable {α : Type u}

namespace Formula

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

def distribDisj : Formula α → Formula α → Formula α
  | conj ψ χ, φ => conj (distribDisj ψ φ) (distribDisj χ φ)   -- (ψ ∧ χ) ∨ φ
  | φ, conj ψ χ => conj (distribDisj φ ψ) (distribDisj φ χ)   -- φ ∨ (ψ ∧ χ)
  | φ, ψ        => disj φ ψ

def distribConj : Formula α → Formula α → Formula α
  | disj ψ χ, φ => disj (distribConj ψ φ) (distribConj χ φ)   -- (ψ ∧ χ) ∨ φ
  | φ, disj ψ χ => disj (distribConj φ ψ) (distribConj φ χ)   -- φ ∨ (ψ ∧ χ)
  | φ, ψ        => conj φ ψ

def toCNF (φ : Formula α) : Formula α :=
  NNFtoCNF (toNNF φ)
  where NNFtoCNF : Formula α → Formula α
  | conj ψ χ => conj (NNFtoCNF ψ) (NNFtoCNF χ)
  | disj ψ χ => distribDisj (NNFtoCNF ψ) (NNFtoCNF χ)
  | φ        => φ

def toDNF (φ : Formula α) : Formula α :=
  NNFtoDNF (toNNF φ)
  where NNFtoDNF : Formula α → Formula α
  | disj ψ χ => disj (NNFtoDNF ψ) (NNFtoDNF χ)
  | conj ψ χ => distribConj (NNFtoDNF ψ) (NNFtoDNF χ)
  | φ        => φ

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

  -- Sorting

def sortFormula [Ord α] : Formula α → Formula α
  | .var a => .var a
  | .top => .top
  | .bot => .bot
  | .neg φ => .neg (sortFormula φ)
  | .conj φ ψ =>
      let φ' := sortFormula φ
      let ψ' := sortFormula ψ
      if compare φ' ψ' == .gt then .conj ψ' φ' else .conj φ' ψ'
  | .disj φ ψ =>
      let φ' := sortFormula φ
      let ψ' := sortFormula ψ
      if compare φ' ψ' == .gt then .disj ψ' φ' else .disj φ' ψ'

@[simp] lemma sortFormula_var [Ord α] (a : α) : sortFormula (var a) = var a := rfl
@[simp] lemma sortFormula_neg [Ord α] (φ : Formula α) : sortFormula (neg φ) =
  neg (sortFormula φ) := rfl
@[simp] lemma sortFormula_conj [Ord α] (φ ψ : Formula α) :
    sortFormula (conj φ ψ) = if compare (sortFormula φ) (sortFormula ψ) ==
    .gt then conj (sortFormula ψ) (sortFormula φ) else conj (sortFormula φ) (sortFormula ψ) := rfl
@[simp] lemma sortFormula_disj [Ord α] (φ ψ : Formula α) :
    sortFormula (disj φ ψ) = if compare (sortFormula φ) (sortFormula ψ) ==
    .gt then disj (sortFormula ψ) (sortFormula φ) else disj (sortFormula φ) (sortFormula ψ) := rfl

end Formula
