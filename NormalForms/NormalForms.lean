import NormalForms.Basic

universe u

variable {α : Type u}

-- Literals Type

inductive Lit (α : Type u) where
  | pos : α → Lit α
  | neg : α → Lit α
/-  Mogelijke toevoeging:
  | top : Lit α
  | bot : Lit α
-/

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


-- CC Type

inductive CC (α : Type u) where
  | lit : Lit α → CC α
  | conj : CC α → CC α → CC α

namespace CC

def toFormula : CC α → Formula α
  | .lit a => a.toFormula
  | .conj φ ψ => Formula.conj (toFormula φ) (toFormula ψ)

instance : Coe (CC α) (Formula α) := ⟨toFormula⟩

def toStringAux [ToString α] : CC α → String
  | .lit a => toString a
  | .conj φ ψ => toStringAux φ ++ " ∧ " ++ toStringAux ψ

instance [ToString α] : ToString (CC α) where
  toString
    | .lit a => toString a
    | .conj φ ψ => "(" ++ toStringAux (.conj φ ψ) ++ ")"

end CC

-- DC Type

inductive DC (α : Type u) where
  | lit : Lit α → DC α
  | disj : DC α → DC α → DC α

namespace DC

def toFormula : DC α → Formula α
  | .lit a => a.toFormula
  | .disj φ ψ => Formula.disj (toFormula φ) (toFormula ψ)

instance : Coe (DC α) (Formula α) := ⟨toFormula⟩

def toStringAux [ToString α] : DC α → String
  | .lit a => toString a
  | .disj φ ψ => toStringAux φ ++ " ∨ " ++ toStringAux ψ

instance [ToString α] : ToString (DC α) where
  toString
    | .lit a => toString a
    | .disj φ ψ => "(" ++ toStringAux (.disj φ ψ) ++ ")"

end DC

-- CNF Type

inductive CNF (α : Type u) where
  | disjclause : DC α → CNF α
  | conj : CNF α → CNF α → CNF α

namespace CNF

private def distributeClause (dc : DC α) : CNF α → CNF α
  | .disjclause a => .disjclause (.disj dc a)
  | .conj φ ψ =>
      .conj (distributeClause dc φ) (distributeClause dc ψ)

def distributeDisj : CNF α → CNF α → CNF α
  | .disjclause dc, rhs => distributeClause dc rhs
  | .conj p q, rhs =>
      .conj (distributeDisj p rhs) (distributeDisj q rhs)

def toFormula : CNF α → Formula α
  | .disjclause dc => dc.toFormula
  | .conj φ ψ => Formula.conj (toFormula φ) (toFormula ψ)

instance : Coe (CNF α) (Formula α) := ⟨toFormula⟩

def toStringAux [ToString α] : CNF α → String
  | .disjclause dc => toString dc
  | .conj φ ψ => toStringAux φ ++ " ∧ " ++ toStringAux ψ

instance [ToString α] : ToString (CNF α) where
  toString
  | .disjclause dc => toString dc
  | .conj φ ψ => "(" ++ toStringAux (.conj φ ψ) ++ ")"

end CNF

-- DNF Type

inductive DNF (α : Type u) where
  | conjclause : CC α → DNF α
  | disj : DNF α → DNF α → DNF α

namespace DNF

private def distributeClause (cc : CC α) : DNF α → DNF α
  | .conjclause a => .conjclause (.conj cc a)
  | .disj φ ψ =>
      .disj (distributeClause cc φ) (distributeClause cc ψ)

def distributeConj : DNF α → DNF α → DNF α
  | .conjclause cc, rhs => distributeClause cc rhs
  | .disj p q, rhs =>
      .disj (distributeConj p rhs) (distributeConj q rhs)

def toFormula : DNF α → Formula α
  | .conjclause cc => cc.toFormula
  | .disj φ ψ => Formula.disj (toFormula φ) (toFormula ψ)

instance : Coe (DNF α) (Formula α) := ⟨toFormula⟩

def toStringAux [ToString α] : DNF α → String
  | .conjclause cc => toString cc
  | .disj φ ψ => toStringAux φ ++ " ∨ " ++ toStringAux ψ

instance [ToString α] : ToString (DNF α) where
  toString
  | .conjclause cc => toString cc
  | .disj φ ψ => "(" ++ toStringAux (.disj φ ψ) ++ ")"

end DNF

-- NNF Type

inductive NNF (α : Type u) where
  | lit : Lit α → NNF α
  | conj : NNF α → NNF α → NNF α
  | disj : NNF α → NNF α → NNF α

namespace NNF

def toFormula : NNF α → Formula α
  | .lit a => a.toFormula
  | .conj φ ψ => Formula.conj (toFormula φ) (toFormula ψ)
  | .disj φ ψ => Formula.disj (toFormula φ) (toFormula ψ)

instance : Coe (NNF α) (Formula α) := ⟨toFormula⟩

def toStringAux [ToString α] : NNF α → String
  | .lit a    => toString a
  | .conj φ ψ => "(" ++ toStringAux φ ++ " ∧ " ++ toStringAux ψ ++ ")"
  | .disj φ ψ => "(" ++ toStringAux φ ++ " ∨ " ++ toStringAux ψ ++ ")"

instance [ToString α] : ToString (NNF α) where
  toString φ := toStringAux φ

def toCNF : (φ : NNF α) → CNF α
  | NNF.lit a => CNF.disjclause (DC.lit a)
  | NNF.conj φ ψ => CNF.conj (toCNF φ) (toCNF ψ)
  | NNF.disj φ ψ => CNF.distributeDisj (toCNF φ) (toCNF ψ)

def toDNF : (φ : NNF α) → DNF α
  | NNF.lit a => DNF.conjclause (CC.lit a)
  | NNF.conj φ ψ => DNF.distributeConj (toDNF φ) (toDNF ψ)
  | NNF.disj φ ψ => DNF.disj (toDNF φ) (toDNF ψ)

end NNF

-- Functions

namespace Formula

mutual
  def toNNF : Formula α → NNF α
    | var a    => NNF.lit (Lit.pos a)
    | neg φ    => toNNFNeg φ
    | conj ψ χ => NNF.conj (toNNF ψ) (toNNF χ)
    | disj ψ χ => NNF.disj (toNNF ψ) (toNNF χ)
    | impl ψ χ => NNF.disj (toNNFNeg ψ) (toNNF χ)
    | iff ψ χ  =>
        NNF.conj
          (NNF.disj (toNNFNeg ψ) (toNNF χ))
          (NNF.disj (toNNFNeg χ) (toNNF ψ))

  private def toNNFNeg : Formula α → NNF α
    | var a    => NNF.lit (Lit.neg a)
    | neg φ    => toNNF φ
    | conj ψ χ => NNF.disj (toNNFNeg ψ) (toNNFNeg χ)
    | disj ψ χ => NNF.conj (toNNFNeg ψ) (toNNFNeg χ)
    | impl ψ χ => NNF.conj (toNNF ψ) (toNNFNeg χ)
    | iff ψ χ  =>
        NNF.disj
          (NNF.conj (toNNF ψ) (toNNFNeg χ))
          (NNF.conj (toNNF χ) (toNNFNeg ψ))
end



def toCNF (φ : Formula α) : CNF α :=
  NNF.toCNF (toNNF φ)

def toDNF (φ : Formula α) : DNF α :=
  NNF.toDNF (toNNF φ)

  -- Lemmata

@[simp] lemma toNNF_var (a : α) : toNNF (var a) = NNF.lit (Lit.pos a) := by simp [toNNF]
@[simp] lemma toNNF_neg (a : α) : toNNF (neg (var a)) = NNF.lit (Lit.neg a)
  := by simp [toNNF, toNNFNeg]
@[simp] lemma toNNF_negneg (φ : Formula α) : toNNF (neg (neg φ)) = toNNF φ
  := by simp [toNNF, toNNFNeg]
@[simp] lemma toNNF_conj (ψ χ : Formula α) : toNNF (conj ψ χ) = NNF.conj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_disj (ψ χ : Formula α) : toNNF (disj ψ χ) = NNF.disj (toNNF ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_impl (ψ χ : Formula α) : toNNF (impl ψ χ) = NNF.disj (toNNFNeg ψ) (toNNF χ)
  := by simp [toNNF]
@[simp] lemma toNNF_iff (ψ χ : Formula α) : toNNF (iff ψ χ) =
  NNF.conj (NNF.disj (toNNFNeg ψ) (toNNF χ)) (NNF.disj (toNNFNeg χ) (toNNF ψ)) := by simp [toNNF]
@[simp] lemma toNNF_negconj (ψ χ : Formula α) : toNNF (neg (conj ψ χ)) =
  NNF.disj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF, toNNFNeg]
@[simp] lemma toNNF_negdisj (ψ χ : Formula α) : toNNF (neg (disj ψ χ)) =
  NNF.conj (toNNF (neg ψ)) (toNNF (neg χ)) := by simp [toNNF, toNNFNeg]
@[simp] lemma toNNF_negimpl (ψ χ : Formula α) : toNNF (neg (impl ψ χ)) =
  NNF.conj (toNNF ψ) (toNNF (neg χ)) := by simp [toNNF, toNNFNeg]
@[simp] lemma toNNF_negiff (ψ χ : Formula α) : toNNF (neg (iff ψ χ)) =
  NNF.disj (NNF.conj (toNNF ψ) (toNNF (neg χ))) (NNF.conj (toNNF χ) (toNNF (neg ψ)))
  := by simp [toNNF, toNNFNeg]

@[simp] lemma toCNF_var (a : α) : toCNF (var a) = CNF.disjclause (DC.lit (Lit.pos a))
  := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_neg (a : α) : toCNF (neg (var a)) = CNF.disjclause (DC.lit (Lit.neg a))
  := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_conj (ψ χ : Formula α) : toCNF (conj ψ χ) = CNF.conj (toCNF ψ) (toCNF χ)
  := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_disj (ψ χ : Formula α) : toCNF (disj ψ χ) = NNF.toCNF (toNNF (disj ψ χ))
  := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_impl (ψ χ : Formula α) : toCNF (impl ψ χ) = NNF.toCNF (toNNF (impl ψ χ))
  := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_iff (ψ χ : Formula α) : toCNF (iff ψ χ) = NNF.toCNF (toNNF (iff ψ χ))
  := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_negconj (ψ χ : Formula α) : toCNF (neg (conj ψ χ)) =
  NNF.toCNF (toNNF (neg (conj ψ χ))) := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_negdisj (ψ χ : Formula α) : toCNF (neg (disj ψ χ)) =
  NNF.toCNF (toNNF (neg (disj ψ χ))) := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_negimpl (ψ χ : Formula α) : toCNF (neg (impl ψ χ)) =
  NNF.toCNF (toNNF (neg (impl ψ χ))) := by simp [toCNF, NNF.toCNF]
@[simp] lemma toCNF_negiff (ψ χ : Formula α) : toCNF (neg (iff ψ χ)) =
  NNF.toCNF (toNNF (neg (iff ψ χ))) := by simp [toCNF, NNF.toCNF]

@[simp] lemma toDNF_var (a : α) : toDNF (var a) = DNF.conjclause (CC.lit (Lit.pos a))
  := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_neg (a : α) : toDNF (neg (var a)) = DNF.conjclause (CC.lit (Lit.neg a))
  := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_conj (ψ χ : Formula α) : toDNF (conj ψ χ) = NNF.toDNF (toNNF (conj ψ χ))
  := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_disj (ψ χ : Formula α) : toDNF (disj ψ χ) = DNF.disj (toDNF ψ) (toDNF χ)
  := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_impl (ψ χ : Formula α) : toDNF (impl ψ χ) = NNF.toDNF (toNNF (impl ψ χ))
  := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_iff (ψ χ : Formula α) : toDNF (iff ψ χ) = NNF.toDNF (toNNF (iff ψ χ))
  := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_negconj (ψ χ : Formula α) : toDNF (neg (conj ψ χ)) =
  NNF.toDNF (toNNF (neg (conj ψ χ))) := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_negdisj (ψ χ : Formula α) : toDNF (neg (disj ψ χ)) =
  NNF.toDNF (toNNF (neg (disj ψ χ))) := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_negimpl (ψ χ : Formula α) : toDNF (neg (impl ψ χ)) =
  NNF.toDNF (toNNF (neg (impl ψ χ))) := by simp [toDNF, NNF.toDNF]
@[simp] lemma toDNF_negiff (ψ χ : Formula α) : toDNF (neg (iff ψ χ)) =
  NNF.toDNF (toNNF (neg (iff ψ χ))) := by simp [toDNF, NNF.toDNF]

end Formula
