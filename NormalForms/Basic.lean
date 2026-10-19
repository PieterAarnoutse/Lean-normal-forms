import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Sum.Order
import Mathlib.Order.Basic
import Mathlib.Order.WellFounded

/-!
# Propositional syntax

This file defines the syntax of propositional formulas over a type of atoms, together
with basic operations such as the variables and subformulas of a formula, syntactic
complexity, substitution, and finite iterated conjunctions and disjunctions.

Since this development has no constants for truth or falsity, the iterated conjunction
and disjunction operations return `Option (Formula α)` on possibly empty collections.
-/

universe u

/-- Propositional formulas over a type `α` of atoms. -/
inductive Formula (α : Type u) where
  /-- An atomic formula. -/
  | var  : α → Formula α
  /-- bot -/
  | bot : Formula α
  /-- Negation. -/
  | neg  : Formula α → Formula α
  /-- Conjunction. -/
  | conj : Formula α → Formula α → Formula α
  /-- Disjunction. -/
  | disj : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

/-- Notation for negation of formulas. -/
prefix:40 "¬ " => neg
/-- Notation for conjunction of formulas. -/
infixr:35 " ∧ " => conj
/-- Notation for disjunction of formulas. -/
infixr:30 " ∨ " => disj

variable {α : Type u}

/-- Tokens for a prefix code on formulas, used to define a computable lexicographic order. -/
private abbrev Token (α : Type u) := Nat ⊕ₗ α

private def tokTag (n : Nat) : Token α := Sum.inl n
private def tokAtom (a : α) : Token α := Sum.inr a

/-- A prefix code for formulas. Ordering formulas by the lexicographic order on these
token lists gives a constructive structural order once the atoms are linearly ordered. -/
private def lexCode : Formula α → List (Token α)
  | var a    => [tokTag 0, tokAtom a]
  | bot      => [tokTag 4]
  | neg φ    => tokTag 1 :: lexCode φ
  | conj φ ψ => tokTag 2 :: lexCode φ ++ lexCode ψ
  | disj φ ψ => tokTag 3 :: lexCode φ ++ lexCode ψ

/-- The computable prefix code used to define the structural lexicographic order on formulas. -/
def orderCode : Formula α → List (Nat ⊕ₗ α) :=
  lexCode

private def codeLength : Formula α → Nat
  | var _    => 2
  | bot      => 1
  | neg φ    => codeLength φ + 1
  | conj φ ψ => codeLength φ + codeLength ψ + 1
  | disj φ ψ => codeLength φ + codeLength ψ + 1

@[simp] private lemma lexCode_length (φ : Formula α) :
    (lexCode φ).length = codeLength φ := by
  induction φ with
  | var a =>
      simp [lexCode, codeLength]
  | bot   =>
      simp [lexCode, codeLength]
  | neg φ ih =>
      simp [lexCode, codeLength, ih]
  | conj φ ψ ihφ ihψ =>
      simp [lexCode, codeLength, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp [lexCode, codeLength, ihφ, ihψ]

private def decodeAux : Nat → List (Token α) → Option (Formula α × List (Token α))
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, Sum.inr _ :: _ => none
  | _ + 1, Sum.inl 0 :: Sum.inr a :: rest => some (var a, rest)
  | _ + 1, Sum.inl 0 :: _ => none
  | n + 1, Sum.inl 1 :: rest => do
      let (φ, rest') <- decodeAux n rest
      pure (neg φ, rest')
  | n + 1, Sum.inl 2 :: rest => do
      let (φ, rest') <- decodeAux n rest
      let (ψ, rest'') <- decodeAux n rest'
      pure (conj φ ψ, rest'')
  | n + 1, Sum.inl 3 :: rest => do
      let (φ, rest') <- decodeAux n rest
      let (ψ, rest'') <- decodeAux n rest'
      pure (disj φ ψ, rest'')
  | _ + 1, Sum.inl 4 :: rest => some (bot, rest)
  | _ + 1, Sum.inl (_ + 5) :: _ => none

private def decode (xs : List (Token α)) : Option (Formula α × List (Token α)) :=
  decodeAux xs.length xs

private lemma decodeAux_encode_append (fuel : Nat) (φ : Formula α) (rest : List (Token α))
    (h : codeLength φ ≤ fuel) :
    decodeAux fuel (lexCode φ ++ rest) = some (φ, rest) := by
  induction φ generalizing fuel rest with
  | var a =>
      cases fuel with
      | zero =>
          cases h
      | succ fuel =>
          simp [lexCode, decodeAux, tokTag, tokAtom]
  | bot =>
      cases fuel with
      | zero =>
          simp [codeLength] at h
      | succ fuel =>
          simp [lexCode, decodeAux, tokTag]
  | neg φ ih =>
      cases fuel with
      | zero =>
          cases h
      | succ fuel =>
          have h' : codeLength φ ≤ fuel := by
            simpa [codeLength] using Nat.le_of_succ_le_succ h
          simp [lexCode, decodeAux, ih fuel rest h', tokTag]
  | conj φ ψ ihφ ihψ =>
      cases fuel with
      | zero =>
          cases h
      | succ fuel =>
          have hsum : codeLength φ + codeLength ψ ≤ fuel := by
            simpa [codeLength, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              Nat.le_of_succ_le_succ h
          have hφ : codeLength φ ≤ fuel := Nat.le_trans (Nat.le_add_right _ _) hsum
          have hψ : codeLength ψ ≤ fuel := Nat.le_trans (Nat.le_add_left _ _) hsum
          simp [lexCode, decodeAux, ihφ fuel (lexCode ψ ++ rest) hφ, ihψ fuel rest hψ,
            List.append_assoc, tokTag]
  | disj φ ψ ihφ ihψ =>
      cases fuel with
      | zero =>
          cases h
      | succ fuel =>
          have hsum : codeLength φ + codeLength ψ ≤ fuel := by
            simpa [codeLength, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              Nat.le_of_succ_le_succ h
          have hφ : codeLength φ ≤ fuel := Nat.le_trans (Nat.le_add_right _ _) hsum
          have hψ : codeLength ψ ≤ fuel := Nat.le_trans (Nat.le_add_left _ _) hsum
          simp [lexCode, decodeAux, ihφ fuel (lexCode ψ ++ rest) hφ, ihψ fuel rest hψ,
            List.append_assoc, tokTag]

private lemma decode_encode_append (φ : Formula α) (rest : List (Token α)) :
    decode (lexCode φ ++ rest) = some (φ, rest) := by
  unfold decode
  apply decodeAux_encode_append
  simp [lexCode_length]

private lemma lexCode_injective : Function.Injective (lexCode (α := α)) := by
  intro φ ψ h
  have hφ : decode (lexCode φ) = some (φ, []) := by
    simpa using decode_encode_append (α := α) φ []
  have hψ : decode (lexCode ψ) = some (ψ, []) := by
    simpa using decode_encode_append (α := α) ψ []
  rw [h] at hφ
  exact congrArg Prod.fst (Option.some.inj (hφ.symm.trans hψ))

instance [LinearOrder α] : LinearOrder (Formula α) :=
  LinearOrder.lift' lexCode lexCode_injective

private def toStringAux [ToString α] : Formula α → String
  | var a    => "p_" ++ toString a
  | bot      => "⊥"
  | neg φ    => "¬" ++ toStringAux φ
  | conj φ ψ => "(" ++ toStringAux φ ++ " ∧ " ++ toStringAux ψ ++ ")"
  | disj φ ψ => "(" ++ toStringAux φ ++ " ∨ " ++ toStringAux ψ ++ ")"

instance [ToString α] : Repr (Formula α) where
  reprPrec φ _ := toStringAux φ

instance [ToString α] : ToString (Formula α) where
  toString φ := toStringAux φ

/-- The formulas of a finset sorted by the canonical structural order. -/
def sorted (Γ : Finset (Formula α)) [LinearOrder α] : List (Formula α) :=
  Γ.sort (· ≤ ·)

private def toStringFinsetAux [ToString α] [LinearOrder α] (Γ : Finset (Formula α)) : String :=
  "{" ++ String.intercalate ", " ((sorted Γ).map toString) ++ "}"

instance [ToString α] [LinearOrder α] : Repr (Finset (Formula α)) where
  reprPrec Γ _ := toStringFinsetAux Γ

instance [ToString α] [LinearOrder α] : ToString (Finset (Formula α)) where
  toString Γ := toStringFinsetAux Γ

/-- `varsList φ` is the list of propositional variables occurring in `φ`,
with repetitions preserved and ordered by recursive traversal. -/
def varsList : Formula α → List α
  | var a    => [a]
  | bot      => []
  | neg φ    => varsList φ
  | conj φ ψ => varsList φ ++ varsList ψ
  | disj φ ψ => varsList φ ++ varsList ψ

/-- `vars φ` is the finite set of propositional variables occurring in `φ`. -/
def vars [DecidableEq α] (φ : Formula α) : Finset α :=
  (varsList φ).toFinset

/-- `subformulaList φ` is the list of subformulas of `φ`,
with repetitions preserved and ordered by recursive traversal.

By convention, a formula counts as a subformula of itself. -/
def subformulaList : Formula α → List (Formula α)
  | var a    => [var a]
  | bot      => []
  | neg φ    => neg φ :: subformulaList φ
  | conj φ ψ => conj φ ψ :: (subformulaList φ ++ subformulaList ψ)
  | disj φ ψ => disj φ ψ :: (subformulaList φ ++ subformulaList ψ)

/-- `subformulas φ` is the finite set of subformulas of `φ`. -/
def subformulas [DecidableEq α] (φ : Formula α) : Finset (Formula α) :=
  (subformulaList φ).toFinset

/-- The syntactic complexity of a formula. -/
def complexity : Formula α → Nat
  | var _    => 0
  | bot      => 0
  | neg φ    => complexity φ + 1
  | conj φ ψ => max (complexity φ) (complexity ψ) + 1
  | disj φ ψ => max (complexity φ) (complexity ψ) + 1

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
  | bot,      i, θ => bot
  | neg φ,    i, θ => neg (subst φ i θ)
  | conj φ ψ, i, θ => conj (subst φ i θ) (subst ψ i θ)
  | disj φ ψ, i, θ => disj (subst φ i θ) (subst ψ i θ)

notation:90 φ "[" i " := " ψ "]" => subst φ i ψ

/-- Iterated disjunction of a list of formulas.

Returns `none` on the empty list, since this syntax has no bottom constant. -/
def bigDisjCons : Formula α → List (Formula α) → Formula α
  | φ, []   => φ
  | φ, ψ :: ψs => Formula.conj φ (bigDisjCons ψ ψs)

def bigDisj : List (Formula α) → Option (Formula α)
  | []      => none
  | φ :: Γ  => some (Γ.foldr Formula.disj φ)

/-- Iterated conjunction of a list of formulas.

Returns `none` on the empty list, since this syntax has no top constant. -/
def bigConjCons : Formula α → List (Formula α) → Formula α
  | φ, []   => φ
  | φ, ψ :: ψs => Formula.conj φ (bigConjCons ψ ψs)

def bigConj : List (Formula α) → Option (Formula α)
  | []      => none
  | φ :: Γ  => some (bigConjCons φ Γ)

#eval bigConj [(var 1), (var 2), (var 3)]

/-- Iterated conjunction of a finite set of formulas in canonical sorted order. -/
def bigConjFinset [LinearOrder α] (Γ : Finset (Formula α)) : Option (Formula α) :=
  bigConj (sorted Γ)

/-- Iterated disjunction of a finite set of formulas in canonical sorted order. -/
def bigDisjFinset [LinearOrder α] (Γ : Finset (Formula α)) : Option (Formula α) :=
  bigDisj (sorted Γ)

/-- Iterated conjunction of a nonempty finite set of formulas in canonical sorted order. -/
def bigConjFinsetNE [LinearOrder α] (Γ : Finset (Formula α)) (h : Γ.Nonempty) : Formula α :=
  let φ := Γ.min' h
  (Γ.erase φ).sort (· ≤ ·) |>.foldr Formula.conj φ

/-- Iterated disjunction of a nonempty finite set of formulas in canonical sorted order. -/
def bigDisjFinsetNE [LinearOrder α] (Γ : Finset (Formula α)) (h : Γ.Nonempty) : Formula α :=
  let φ := Γ.min' h
  (Γ.erase φ).sort (· ≤ ·) |>.foldr Formula.disj φ

/-- Canonical finite conjunction in sorted order. Returns `none` on the empty finset. -/
notation:max "⋀ " Γ => bigConjFinset Γ

/-- Canonical finite disjunction in sorted order. Returns `none` on the empty finset. -/
notation:max "⋁ " Γ => bigDisjFinset Γ

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

@[simp]
lemma bigConj_nil : (bigConj ([] : List (Formula α))) = none := rfl

@[simp]
lemma bigDisj_nil : (bigDisj ([] : List (Formula α))) = none := rfl

@[simp]
lemma bigConj_cons (φ : Formula α) (Γ : List (Formula α)) :
    bigConj (φ :: Γ) = some (bigConjCons φ Γ) := rfl

@[simp]
lemma bigDisj_cons (φ : Formula α) (Γ : List (Formula α)) :
    bigDisj (φ :: Γ) = some (Γ.foldr Formula.disj φ) := rfl

end Formula
