import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.String.Basic

/-!
# Propositional syntax

This file defines the syntax of propositional formulas over a type of atoms, together
with basic operations such as the variables and subformulas of a formula, syntactic
complexity, substitution, and finite iterated conjunctions and disjunctions.

The formula syntax includes truth and falsity constants, so iterated conjunctions and
disjunctions are defined for empty collections as well.
-/

universe u

/-- Propositional formulas over a type `α` of atoms. -/
inductive Formula (α : Type u) where
  /-- An atomic formula. -/
  | var  : α → Formula α
  /-- Negation. -/
  | neg  : Formula α → Formula α
  /-- Conjunction. -/
  | conj : Formula α → Formula α → Formula α
  /-- Disjunction. -/
  | disj : Formula α → Formula α → Formula α
  /-- Truth. -/
  | top : Formula α
  /-- Falsity. -/
  | bot : Formula α
  deriving DecidableEq, Ord
  /-
  Both the `DecidableEq` and `Ord` instances are derived from the inductive definition of `Formula`.
  The order is defined by the order of the constructors, and
  then recursively on the arguments. This gives a canonical structural order on formulas.
  -/

namespace Formula

/-- Coercion from atoms to formulas. -/
instance : Coe (α) (Formula α) := ⟨var⟩

/-- Notation for negation of formulas. -/
prefix:40 "¬ " => neg
/-- Notation for conjunction of formulas. -/
infixr:35 " ∧ " => conj
/-- Notation for disjunction of formulas. -/
infixr:30 " ∨ " => disj

private def toStringAux [ToString α] : Formula α → String
  | var a    => toString a
  | neg φ    => "¬" ++ toStringAux φ
  | conj φ ψ => "(" ++ toStringAux φ ++ " ∧ " ++ toStringAux ψ ++ ")"
  | disj φ ψ => "(" ++ toStringAux φ ++ " ∨ " ++ toStringAux ψ ++ ")"
  | top      => "⊤"
  | bot      => "⊥"

instance [ToString α] : Repr (Formula α) where
  reprPrec φ _ := toStringAux φ

instance [ToString α] : ToString (Formula α) where
  toString φ := toStringAux φ

-- Big operators

/-- Iterated disjunction of a list of formulas; the empty disjunction is false. -/
def bigDisj : List (Formula α) → Formula α
  | []      => bot
  | φ :: Γ  => Γ.foldl Formula.disj φ

/-- Iterated conjunction of a list of formulas; the empty conjunction is true. -/
def bigConj : List (Formula α) → Formula α
  | []      => top
  | φ :: Γ  => Γ.foldl Formula.conj φ


notation:max "⋀ " Γ => bigConj Γ
notation:max "⋁ " Γ => bigDisj Γ

@[simp]
lemma bigConj_nil : (bigConj ([] : List (Formula α))) = top := rfl

@[simp]
lemma bigDisj_nil : (bigDisj ([] : List (Formula α))) = bot := rfl

@[simp]
lemma bigConj_cons (φ : Formula α) (Γ : List (Formula α)) :
  bigConj (φ :: Γ) = Γ.foldl Formula.conj φ := rfl

@[simp]
lemma bigDisj_cons (φ : Formula α) (Γ : List (Formula α)) :
  bigDisj (φ :: Γ) = Γ.foldl Formula.disj φ := rfl

-- Restanten die niet overbodig zijn

/-- `varsList φ` is the list of propositional variables occurring in `φ`,
with repetitions preserved and ordered by recursive traversal. -/
def varsList : Formula α → List α
  | var a    => [a]
  | neg φ    => varsList φ
  | conj φ ψ => varsList φ ++ varsList ψ
  | disj φ ψ => varsList φ ++ varsList ψ
  | top      => []
  | bot      => []

/-- `vars φ` is the finite set of propositional variables occurring in `φ`. -/
def vars [DecidableEq α] (φ : Formula α) : Finset α :=
  (varsList φ).toFinset

/-- `subformulaList φ` is the list of subformulas of `φ`,
with repetitions preserved and ordered by recursive traversal.

By convention, a formula counts as a subformula of itself. -/
def subformulaList : Formula α → List (Formula α)
  | var a    => [var a]
  | neg φ    => neg φ :: subformulaList φ
  | conj φ ψ => conj φ ψ :: (subformulaList φ ++ subformulaList ψ)
  | disj φ ψ => disj φ ψ :: (subformulaList φ ++ subformulaList ψ)
  | top      => [top]
  | bot      => [bot]

/-- `subformulas φ` is the finite set of subformulas of `φ`. -/
def subformulas [DecidableEq α] (φ : Formula α) : Finset (Formula α) :=
  (subformulaList φ).toFinset

/-- The syntactic complexity of a formula. -/
def complexity : Formula α → Nat
  | var _    => 0
  | neg φ    => complexity φ + 1
  | conj φ ψ => max (complexity φ) (complexity ψ) + 1
  | disj φ ψ => max (complexity φ) (complexity ψ) + 1
  | top      => 0
  | bot      => 0

/-- Notation for the syntactic complexity of a formula. -/
notation "c(" φ ")" => complexity φ

/-- The strict order on formulas induced by syntactic complexity. -/
def ltComplexity (φ ψ : Formula α) : Prop := c(φ) < c(ψ)

notation:50 φ " ≺ " ψ => ltComplexity φ ψ

/-- The complexity order on formulas is well-founded. -/
lemma wf_ltComplexity : WellFounded (ltComplexity : Formula α → Formula α → Prop) := by
  simpa [ltComplexity] using (measure complexity).wf

/-- Induction on syntactic complexity. -/
def inductionOnComplexity {P : Formula α → Prop} (φ : Formula α)
    (h : ∀ ψ, (∀ χ, c(χ) < c(ψ) → P χ) → P ψ) : P φ :=
  WellFounded.induction wf_ltComplexity φ h

/-- Substitution of `θ` for the variable `i` in a formula. -/
def subst [DecidableEq α] : Formula α → α → Formula α → Formula α
  | var j,    i, θ => if j = i then θ else var j
  | neg φ,    i, θ => neg (subst φ i θ)
  | conj φ ψ, i, θ => conj (subst φ i θ) (subst ψ i θ)
  | disj φ ψ, i, θ => disj (subst φ i θ) (subst ψ i θ)
  | top,      _, _ => top
  | bot,      _, _ => bot

notation:90 φ "[" i " := " ψ "]" => subst φ i ψ



@[simp] lemma varsList_var (a : α) : varsList (var a) = [a] := rfl
@[simp] lemma varsList_neg (φ : Formula α) : varsList (neg φ) = varsList φ := rfl
@[simp] lemma varsList_conj (φ ψ : Formula α) :
    varsList (φ ∧ ψ) = varsList φ ++ varsList ψ := rfl
@[simp] lemma varsList_disj (φ ψ : Formula α) :
    varsList (φ ∨ ψ) = varsList φ ++ varsList ψ := rfl

@[simp] lemma subformulaList_var (a : α) : subformulaList (var a) = [var a] := rfl
@[simp] lemma subformulaList_neg (φ : Formula α) :
    subformulaList (neg φ) = neg φ :: subformulaList φ := rfl
@[simp] lemma subformulaList_conj (φ ψ : Formula α) :
    subformulaList (φ ∧ ψ) = (φ ∧ ψ) :: (subformulaList φ ++ subformulaList ψ) := rfl
@[simp] lemma subformulaList_disj (φ ψ : Formula α) :
    subformulaList (φ ∨ ψ) = (φ ∨ ψ) :: (subformulaList φ ++ subformulaList ψ) := rfl

@[simp] lemma complexity_var (a : α) : c(var a) = 0 := rfl
@[simp] lemma complexity_neg (φ : Formula α) : c(neg φ) = c(φ) + 1 := rfl
@[simp] lemma complexity_conj (φ ψ : Formula α) :
    c(φ ∧ ψ) = max (c(φ)) (c(ψ)) + 1 := rfl
@[simp] lemma complexity_disj (φ ψ : Formula α) :
    c(φ ∨ ψ) = max (c(φ)) (c(ψ)) + 1 := rfl

@[simp]
lemma subst_var_eq [DecidableEq α] (i : α) (φ : Formula α) :
    (var i)[i := φ] = φ := by
  simp [subst]

@[simp]
lemma subst_var_ne [DecidableEq α] (i j : α) (h : j ≠ i) (φ : Formula α) :
    (var j)[i := φ] = var j := by
  simp [subst, h]

@[simp]
lemma subst_neg [DecidableEq α] (φ ψ : Formula α) (i : α) :
    (¬ φ)[i := ψ] = (¬(φ[i := ψ])) := by
  rfl

@[simp]
lemma subst_conj [DecidableEq α] (φ ψ θ : Formula α) (i : α) :
    (φ ∧ ψ)[i := θ] = (φ[i := θ] ∧ ψ[i := θ]) := by
  rfl

@[simp]
lemma subst_disj [DecidableEq α] (φ ψ θ : Formula α) (i : α) :
    (φ ∨ ψ)[i := θ] = (φ[i := θ] ∨ ψ[i := θ]) := by
  rfl


end Formula
