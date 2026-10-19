import NormalForms.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic

/-!
# Normal forms for propositional syntax

This file defines separate datatypes for literals and negation normal forms, together
with conjunctive clauses, disjunctive clauses, disjunctive normal forms, and conjunctive
normal forms.

Clauses and normal forms are stored as nonempty *lists*, so order and repetitions are
preserved. Laws such as commutativity and idempotence therefore hold only up to the
equivalence relation `≈` (same literals / same clauses up to `≈`), not up to `=`.

Since the basic syntax has no constants for truth or falsity, conversions of clauses
and normal forms back to formulas use the nonemptiness proofs stored in the structures.

Assumes `NormalForms.Basic` provides the order-preserving folds
`Formula.bigConjCons` and `Formula.bigDisjCons` (head `φ`, tail `ψs`, right-nested).
-/

universe u

namespace Formula

/-! ### Generic list helpers -/

section ListHelpers

variable {β γ δ : Type*}

/-- All pairwise combinations `f x y` with `x ∈ xs`, `y ∈ ys`, in row-major order. -/
def pairWith (f : β → γ → δ) (xs : List β) (ys : List γ) : List δ :=
  xs.flatMap fun x => ys.map (f x)

@[simp] lemma pairWith_nil_left (f : β → γ → δ) (ys : List γ) :
    pairWith f [] ys = [] := by
  simp [pairWith]

@[simp] lemma pairWith_cons (f : β → γ → δ) (x : β) (xs : List β) (ys : List γ) :
    pairWith f (x :: xs) ys = ys.map (f x) ++ pairWith f xs ys := by
  simp [pairWith]

lemma pairWith_append_left (f : β → γ → δ) (xs xs' : List β) (ys : List γ) :
    pairWith f (xs ++ xs') ys = pairWith f xs ys ++ pairWith f xs' ys := by
  simp [pairWith, List.flatMap_append]

@[simp] lemma mem_pairWith {f : β → γ → δ} {xs : List β} {ys : List γ} {z : δ} :
    z ∈ pairWith f xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, f x y = z := by
  simp [pairWith, List.mem_flatMap, List.mem_map]

lemma pairWith_ne_nil {f : β → γ → δ} {xs : List β} {ys : List γ}
    (hx : xs ≠ []) (hy : ys ≠ []) : pairWith f xs ys ≠ [] := by
  cases xs with
  | nil => exact absurd rfl hx
  | cons x xs =>
    cases ys with
    | nil => exact absurd rfl hy
    | cons y ys => simp

/-- Mapping over `pairWith` can be pushed inside, given a compatibility law. -/
lemma map_pairWith {β' γ' δ' : Type*} {f : β → γ → δ} {f' : β' → γ' → δ'}
    {g : δ → δ'} {g₁ : β → β'} {g₂ : γ → γ'}
    (h : ∀ x y, g (f x y) = f' (g₁ x) (g₂ y)) (xs : List β) (ys : List γ) :
    (pairWith f xs ys).map g = pairWith f' (xs.map g₁) (ys.map g₂) := by
  induction xs with
  | nil => simp [pairWith]
  | cons x xs ih =>
    have key : ∀ zs : List γ,
        (zs.map (f x)).map g = (zs.map g₂).map (f' (g₁ x)) := by
      intro zs
      induction zs with
      | nil => rfl
      | cons z zs ihz => simp only [List.map_cons, h, ihz]
    rw [pairWith_cons, List.map_append, ih, List.map_cons, pairWith_cons, key]

end ListHelpers

variable {α : Type u}

/-- A literal is either a positive or a negative occurrence of an atom. -/
inductive Literal (α : Type u) where
  | pos : α → Literal α
  | neg : α → Literal α
  deriving DecidableEq

namespace Literal

/-- The underlying atom of a literal. -/
def atom : Literal α → α
  | pos a => a
  | neg a => a

/-- The formula corresponding to a literal. -/
def toFormula : Literal α → Formula α
  | pos a => .var a
  | neg a => .neg (.var a)

instance : Coe (Literal α) (Formula α) := ⟨toFormula⟩

@[simp] lemma coe_pos (a : α) : ((pos a : Literal α) : Formula α) = Formula.var a := rfl
@[simp] lemma coe_neg (a : α) :
    ((neg a : Literal α) : Formula α) = Formula.neg (Formula.var a) := rfl

/-- Complementation of literals. -/
def compl : Literal α → Literal α
  | pos a => neg a
  | neg a => pos a

/-- Bar notation for literal complementation. -/
prefix:max "¯" => compl

@[simp] lemma atom_pos (a : α) : atom (pos a) = a := rfl
@[simp] lemma atom_neg (a : α) : atom (neg a) = a := rfl
@[simp] lemma atom_compl (ℓ : Literal α) : atom (¯ℓ) = atom ℓ := by
  cases ℓ <;> rfl

@[simp] lemma toFormula_pos (a : α) : toFormula (pos a : Literal α) = Formula.var a := rfl
@[simp] lemma toFormula_neg (a : α) :
    toFormula (neg a : Literal α) = Formula.neg (Formula.var a) := rfl

@[simp] lemma compl_pos (a : α) : ¯(pos a : Literal α) = neg a := rfl
@[simp] lemma compl_neg (a : α) : ¯(neg a : Literal α) = pos a := rfl
@[simp] lemma compl_compl (ℓ : Literal α) : ¯(¯ℓ) = ℓ := by
  cases ℓ <;> rfl
@[simp] lemma compl_inj (ℓ₁ ℓ₂ : Literal α) : ¯ℓ₁ = ¯ℓ₂ ↔ ℓ₁ = ℓ₂ := by
  constructor
  · intro h
    simpa using congrArg compl h
  · intro h
    simp [h]

/-- Complementing every literal of a list twice gives back the list. -/
@[simp] lemma map_compl_map_compl (l : List (Literal α)) :
    (l.map compl).map compl = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, compl_compl, ih]

@[simp] lemma toFormula_compl_pos (a : α) :
    ((¯(pos a : Literal α) : Literal α) : Formula α) = Formula.neg (Formula.var a) := rfl
@[simp] lemma toFormula_compl_neg (a : α) :
    ((¯(neg a : Literal α) : Literal α) : Formula α) = Formula.var a := rfl

lemma toFormula_injective : Function.Injective (toFormula (α := α)) := by
  intro ℓ₁ ℓ₂ h
  cases ℓ₁ <;> cases ℓ₂ <;> cases h <;> rfl

@[simp] lemma pos_injective {a b : α} : (pos a : Literal α) = pos b ↔ a = b := by
  constructor <;> intro h <;> cases h <;> rfl

@[simp] lemma neg_injective {a b : α} : (neg a : Literal α) = neg b ↔ a = b := by
  constructor <;> intro h <;> cases h <;> rfl

instance [LinearOrder α] : LinearOrder (Literal α) :=
  LinearOrder.lift' toFormula toFormula_injective

instance [ToString α] : Repr (Literal α) where
  reprPrec ℓ n := Repr.reprPrec (ℓ : Formula α) n

instance [ToString α] : ToString (Literal α) where
  toString ℓ := toString (ℓ : Formula α)

/-- The embedding of literals into formulas. -/
def toFormulaEmbedding : Literal α ↪ Formula α :=
  ⟨toFormula, toFormula_injective⟩

/-- The involutive complementation of literals as an embedding. -/
def complEmbedding : Literal α ↪ Literal α :=
  ⟨compl, fun _ _ h => (compl_inj _ _).1 h⟩

end Literal

/-- A conjunctive clause is a nonempty list of literals. -/
structure ConjunctiveClause (α : Type u) where
  lits : List (Literal α)
  nonempty : lits ≠ []
  deriving DecidableEq

/-- A disjunctive clause is a nonempty list of literals. -/
structure DisjunctiveClause (α : Type u) where
  lits : List (Literal α)
  nonempty : lits ≠ []
  deriving DecidableEq

namespace ConjunctiveClause

/-- Two clauses are equivalent when they contain the same literals,
ignoring order and repetitions. -/
def Equiv (C D : ConjunctiveClause α) : Prop :=
  ∀ ℓ, ℓ ∈ C.lits ↔ ℓ ∈ D.lits

instance setoid : Setoid (ConjunctiveClause α) where
  r := Equiv
  iseqv := ⟨fun _ _ => Iff.rfl, fun h ℓ => (h ℓ).symm, fun h₁ h₂ ℓ => (h₁ ℓ).trans (h₂ ℓ)⟩

lemma equiv_iff {C D : ConjunctiveClause α} :
    C ≈ D ↔ ∀ ℓ, ℓ ∈ C.lits ↔ ℓ ∈ D.lits := Iff.rfl

lemma equiv_of_eq {C D : ConjunctiveClause α} (h : C = D) : C ≈ D := by
  subst h
  exact Setoid.refl _

instance : Coe (ConjunctiveClause α) (List (Literal α)) := ⟨ConjunctiveClause.lits⟩

@[simp] lemma lits_mk (Γ : List (Literal α)) (h : Γ ≠ []) :
    (ConjunctiveClause.mk Γ h).lits = Γ := rfl

@[simp] lemma nonempty_coe (C : ConjunctiveClause α) :
    (C : List (Literal α)) ≠ [] := C.nonempty

@[ext] lemma ext {C D : ConjunctiveClause α} (h : C.lits = D.lits) : C = D := by
  cases C
  cases D
  cases h
  rfl

lemma lits_injective : Function.Injective (ConjunctiveClause.lits (α := α)) :=
  fun _ _ h => ext h

@[simp] lemma mem_coe {C : ConjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (C : List (Literal α)) ↔ ℓ ∈ C.lits :=
  Iff.rfl

def singleton (ℓ : Literal α) : ConjunctiveClause α := ⟨[ℓ], by simp⟩

def merge (C D : ConjunctiveClause α) : ConjunctiveClause α :=
  ⟨C.lits ++ D.lits, by simp [C.nonempty]⟩

@[simp] lemma lits_singleton (ℓ : Literal α) :
    (singleton ℓ).lits = [ℓ] := rfl

@[simp] lemma lits_merge (C D : ConjunctiveClause α) :
    (merge C D).lits = C.lits ++ D.lits := rfl

@[simp] lemma mem_singleton {ℓ m : Literal α} :
    m ∈ (singleton ℓ).lits ↔ m = ℓ := List.mem_singleton

@[simp] lemma mem_merge {C D : ConjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (merge C D).lits ↔ ℓ ∈ C.lits ∨ ℓ ∈ D.lits := List.mem_append

/-- Merging is commutative up to `≈` (the literal order differs). -/
lemma merge_comm (C D : ConjunctiveClause α) : merge C D ≈ merge D C := by
  refine equiv_iff.2 fun ℓ => ?_
  simp only [lits_merge, List.mem_append]
  exact or_comm

/-- Merging is associative (this is a genuine equality for lists). -/
@[simp] lemma merge_assoc (C D E : ConjunctiveClause α) :
    merge (merge C D) E = merge C (merge D E) := by
  apply ext
  simp only [lits_merge, List.append_assoc]

/-- Merging is idempotent up to `≈` (repetitions remain in the list). -/
lemma merge_idem (C : ConjunctiveClause α) : merge C C ≈ C := by
  refine equiv_iff.2 fun ℓ => ?_
  simp only [lits_merge, List.mem_append, or_self]

lemma merge_absorb_distrib (C D E : ConjunctiveClause α) :
    merge (merge C D) (merge C E) ≈ merge C (merge D E) := by
  refine equiv_iff.2 fun ℓ => ?_
  simp only [lits_merge, List.mem_append]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

/-- Merging respects `≈` in both arguments. -/
lemma merge_congr {C C' D D' : ConjunctiveClause α} (hC : C ≈ C') (hD : D ≈ D') :
    merge C D ≈ merge C' D' := by
  refine equiv_iff.2 fun ℓ => ?_
  have h₁ : ℓ ∈ C.lits ↔ ℓ ∈ C'.lits := equiv_iff.1 hC ℓ
  have h₂ : ℓ ∈ D.lits ↔ ℓ ∈ D'.lits := equiv_iff.1 hD ℓ
  simp only [lits_merge, List.mem_append]
  rw [h₁, h₂]

/-- The formula `ℓ₁ ∧ (ℓ₂ ∧ (… ∧ ℓₙ))`, in the order of the list. -/
def toFormula (C : ConjunctiveClause α) : Formula α :=
  match h : C.lits with
  | []      => absurd h C.nonempty
  | ℓ :: ls => bigConjCons ℓ.toFormula (ls.map Literal.toFormula)

instance : Coe (ConjunctiveClause α) (Formula α) := ⟨toFormula⟩

@[simp] lemma coe_coe (C : ConjunctiveClause α) :
    ((C : Formula α)) = toFormula C := rfl

@[simp] lemma toFormula_mk (ℓ : Literal α) (ls : List (Literal α)) (h : ℓ :: ls ≠ []) :
    toFormula ⟨ℓ :: ls, h⟩ =
      bigConjCons ℓ.toFormula (ls.map Literal.toFormula) := rfl

@[simp] lemma toFormula_singleton (ℓ : Literal α) :
    toFormula (singleton ℓ) = (ℓ : Formula α) := rfl

instance [ToString α] : Repr (ConjunctiveClause α) where
  reprPrec C n := Repr.reprPrec (C : Formula α) n

instance [ToString α] : ToString (ConjunctiveClause α) where
  toString C := toString (C : Formula α)

end ConjunctiveClause

namespace DisjunctiveClause

/-- Two clauses are equivalent when they contain the same literals,
ignoring order and repetitions. -/
def Equiv (C D : DisjunctiveClause α) : Prop :=
  ∀ ℓ, ℓ ∈ C.lits ↔ ℓ ∈ D.lits

instance setoid : Setoid (DisjunctiveClause α) where
  r := Equiv
  iseqv := ⟨fun _ _ => Iff.rfl, fun h ℓ => (h ℓ).symm, fun h₁ h₂ ℓ => (h₁ ℓ).trans (h₂ ℓ)⟩

lemma equiv_iff {C D : DisjunctiveClause α} :
    C ≈ D ↔ ∀ ℓ, ℓ ∈ C.lits ↔ ℓ ∈ D.lits := Iff.rfl

lemma equiv_of_eq {C D : DisjunctiveClause α} (h : C = D) : C ≈ D := by
  subst h
  exact Setoid.refl _

instance : Coe (DisjunctiveClause α) (List (Literal α)) := ⟨DisjunctiveClause.lits⟩

@[simp] lemma lits_mk (Γ : List (Literal α)) (h : Γ ≠ []) :
    (DisjunctiveClause.mk Γ h).lits = Γ := rfl

@[simp] lemma nonempty_coe (C : DisjunctiveClause α) :
    (C : List (Literal α)) ≠ [] := C.nonempty

@[ext] lemma ext {C D : DisjunctiveClause α} (h : C.lits = D.lits) : C = D := by
  cases C
  cases D
  cases h
  rfl

lemma lits_injective : Function.Injective (DisjunctiveClause.lits (α := α)) :=
  fun _ _ h => ext h

@[simp] lemma mem_coe {C : DisjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (C : List (Literal α)) ↔ ℓ ∈ C.lits :=
  Iff.rfl

def singleton (ℓ : Literal α) : DisjunctiveClause α := ⟨[ℓ], by simp⟩

def merge (C D : DisjunctiveClause α) : DisjunctiveClause α :=
  ⟨C.lits ++ D.lits, by simp [C.nonempty]⟩

@[simp] lemma lits_singleton (ℓ : Literal α) :
    (singleton ℓ).lits = [ℓ] := rfl

@[simp] lemma lits_merge (C D : DisjunctiveClause α) :
    (merge C D).lits = C.lits ++ D.lits := rfl

@[simp] lemma mem_singleton {ℓ m : Literal α} :
    m ∈ (singleton ℓ).lits ↔ m = ℓ := List.mem_singleton

@[simp] lemma mem_merge {C D : DisjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (merge C D).lits ↔ ℓ ∈ C.lits ∨ ℓ ∈ D.lits := List.mem_append

/-- Merging is commutative up to `≈` (the literal order differs). -/
lemma merge_comm (C D : DisjunctiveClause α) : merge C D ≈ merge D C := by
  refine equiv_iff.2 fun ℓ => ?_
  simp only [lits_merge, List.mem_append]
  exact or_comm

/-- Merging is associative (this is a genuine equality for lists). -/
@[simp] lemma merge_assoc (C D E : DisjunctiveClause α) :
    merge (merge C D) E = merge C (merge D E) := by
  apply ext
  simp only [lits_merge, List.append_assoc]

/-- Merging is idempotent up to `≈` (repetitions remain in the list). -/
lemma merge_idem (C : DisjunctiveClause α) : merge C C ≈ C := by
  refine equiv_iff.2 fun ℓ => ?_
  simp only [lits_merge, List.mem_append, or_self]

lemma merge_absorb_distrib (C D E : DisjunctiveClause α) :
    merge (merge C D) (merge C E) ≈ merge C (merge D E) := by
  refine equiv_iff.2 fun ℓ => ?_
  simp only [lits_merge, List.mem_append]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

/-- Merging respects `≈` in both arguments. -/
lemma merge_congr {C C' D D' : DisjunctiveClause α} (hC : C ≈ C') (hD : D ≈ D') :
    merge C D ≈ merge C' D' := by
  refine equiv_iff.2 fun ℓ => ?_
  have h₁ : ℓ ∈ C.lits ↔ ℓ ∈ C'.lits := equiv_iff.1 hC ℓ
  have h₂ : ℓ ∈ D.lits ↔ ℓ ∈ D'.lits := equiv_iff.1 hD ℓ
  simp only [lits_merge, List.mem_append]
  rw [h₁, h₂]

/-- The formula `ℓ₁ ∨ (ℓ₂ ∨ (… ∨ ℓₙ))`, in the order of the list. -/
def toFormula (C : DisjunctiveClause α) : Formula α :=
  match h : C.lits with
  | []      => absurd h C.nonempty
  | ℓ :: ls => bigDisjCons ℓ.toFormula (ls.map Literal.toFormula)

instance : Coe (DisjunctiveClause α) (Formula α) := ⟨toFormula⟩

@[simp] lemma coe_coe (C : DisjunctiveClause α) :
    ((C : Formula α)) = toFormula C := rfl

@[simp] lemma toFormula_mk (ℓ : Literal α) (ls : List (Literal α)) (h : ℓ :: ls ≠ []) :
    toFormula ⟨ℓ :: ls, h⟩ =
      bigDisjCons ℓ.toFormula (ls.map Literal.toFormula) := rfl

@[simp] lemma toFormula_singleton (ℓ : Literal α) :
    toFormula (singleton ℓ) = (ℓ : Formula α) := rfl

instance [ToString α] : Repr (DisjunctiveClause α) where
  reprPrec C n := Repr.reprPrec (C : Formula α) n

instance [ToString α] : ToString (DisjunctiveClause α) where
  toString C := toString (C : Formula α)

end DisjunctiveClause

namespace ConjunctiveClause

/-- Complement of a conjunctive clause: complement every literal, in the same order. -/
def compl (C : ConjunctiveClause α) : DisjunctiveClause α :=
  ⟨C.lits.map Literal.compl, by simp [C.nonempty]⟩

@[simp] lemma lits_compl (C : ConjunctiveClause α) :
    (compl C).lits = C.lits.map Literal.compl := rfl

@[simp] lemma compl_singleton (ℓ : Literal α) :
    compl (singleton ℓ) = DisjunctiveClause.singleton (¯ℓ) := rfl

@[simp] lemma compl_merge (C D : ConjunctiveClause α) :
    compl (merge C D) = DisjunctiveClause.merge (compl C) (compl D) := by
  apply DisjunctiveClause.ext
  simp only [lits_compl, lits_merge, DisjunctiveClause.lits_merge, List.map_append]

end ConjunctiveClause

namespace DisjunctiveClause

/-- Complement of a disjunctive clause: complement every literal, in the same order. -/
def compl (C : DisjunctiveClause α) : ConjunctiveClause α :=
  ⟨C.lits.map Literal.compl, by simp [C.nonempty]⟩

@[simp] lemma lits_compl (C : DisjunctiveClause α) :
    (compl C).lits = C.lits.map Literal.compl := rfl

@[simp] lemma compl_singleton (ℓ : Literal α) :
    compl (singleton ℓ) = ConjunctiveClause.singleton (¯ℓ) := rfl

@[simp] lemma compl_merge (C D : DisjunctiveClause α) :
    compl (merge C D) = ConjunctiveClause.merge (compl C) (compl D) := by
  apply ConjunctiveClause.ext
  simp only [lits_compl, lits_merge, ConjunctiveClause.lits_merge, List.map_append]

@[simp] lemma compl_compl (C : DisjunctiveClause α) :
    ConjunctiveClause.compl (compl C) = C := by
  apply ext
  simp only [ConjunctiveClause.lits_compl, lits_compl, Literal.map_compl_map_compl]

def complEmbedding : DisjunctiveClause α ↪ ConjunctiveClause α :=
  ⟨compl, fun _ _ h => by
    have h' := congrArg ConjunctiveClause.compl h
    simpa using h'⟩

end DisjunctiveClause

namespace ConjunctiveClause

@[simp] lemma compl_compl (C : ConjunctiveClause α) :
    DisjunctiveClause.compl (compl C) = C := by
  apply ext
  simp only [DisjunctiveClause.lits_compl, lits_compl, Literal.map_compl_map_compl]

def complEmbedding : ConjunctiveClause α ↪ DisjunctiveClause α :=
  ⟨compl, fun _ _ h => by
    have h' := congrArg DisjunctiveClause.compl h
    simpa using h'⟩

end ConjunctiveClause

/-- A disjunctive normal form is a nonempty list of conjunctive clauses. -/
structure DisjunctiveNormalForm (α : Type u) where
  clauses : List (ConjunctiveClause α)
  nonempty : clauses ≠ []
  deriving DecidableEq

/-- A conjunctive normal form is a nonempty list of disjunctive clauses. -/
structure ConjunctiveNormalForm (α : Type u) where
  clauses : List (DisjunctiveClause α)
  nonempty : clauses ≠ []
  deriving DecidableEq

abbrev DNF (α : Type u) := DisjunctiveNormalForm α
abbrev CNF (α : Type u) := ConjunctiveNormalForm α

namespace DisjunctiveNormalForm

/-- Two DNFs are equivalent when every clause of one is `≈` to a clause of the other. -/
def Equiv (D E : DisjunctiveNormalForm α) : Prop :=
  (∀ C ∈ D.clauses, ∃ C' ∈ E.clauses, C ≈ C') ∧
  (∀ C ∈ E.clauses, ∃ C' ∈ D.clauses, C ≈ C')

instance setoid : Setoid (DisjunctiveNormalForm α) where
  r := Equiv
  iseqv := by
    refine ⟨fun D => ⟨fun C hC => ⟨C, hC, Setoid.refl C⟩,
        fun C hC => ⟨C, hC, Setoid.refl C⟩⟩,
      fun h => ⟨h.2, h.1⟩, fun h₁ h₂ => ⟨?_, ?_⟩⟩
    · intro C hC
      obtain ⟨C', hC', e₁⟩ := h₁.1 C hC
      obtain ⟨C'', hC'', e₂⟩ := h₂.1 C' hC'
      exact ⟨C'', hC'', Setoid.trans e₁ e₂⟩
    · intro C hC
      obtain ⟨C', hC', e₁⟩ := h₂.2 C hC
      obtain ⟨C'', hC'', e₂⟩ := h₁.2 C' hC'
      exact ⟨C'', hC'', Setoid.trans e₁ e₂⟩

lemma equiv_iff {D E : DisjunctiveNormalForm α} :
    D ≈ E ↔ (∀ C ∈ D.clauses, ∃ C' ∈ E.clauses, C ≈ C') ∧
      (∀ C ∈ E.clauses, ∃ C' ∈ D.clauses, C ≈ C') := Iff.rfl

/-- DNFs with exactly the same clauses are equivalent. -/
lemma equiv_of_mem_iff {D E : DisjunctiveNormalForm α}
    (h : ∀ C, C ∈ D.clauses ↔ C ∈ E.clauses) : D ≈ E :=
  equiv_iff.2 ⟨fun C hC => ⟨C, (h C).1 hC, Setoid.refl C⟩,
    fun C hC => ⟨C, (h C).2 hC, Setoid.refl C⟩⟩

instance : Coe (DisjunctiveNormalForm α) (List (ConjunctiveClause α)) :=
  ⟨DisjunctiveNormalForm.clauses⟩

@[simp] lemma clauses_mk (Γ : List (ConjunctiveClause α)) (h : Γ ≠ []) :
    (DisjunctiveNormalForm.mk Γ h).clauses = Γ := rfl

@[simp] lemma nonempty_coe (D : DisjunctiveNormalForm α) :
    (D : List (ConjunctiveClause α)) ≠ [] := D.nonempty

@[ext] lemma ext {D E : DisjunctiveNormalForm α} (h : D.clauses = E.clauses) : D = E := by
  cases D
  cases E
  cases h
  rfl

@[simp] lemma mem_coe {D : DisjunctiveNormalForm α} {C : ConjunctiveClause α} :
    C ∈ (D : List (ConjunctiveClause α)) ↔ C ∈ D.clauses := Iff.rfl

def singleton (C : ConjunctiveClause α) : DisjunctiveNormalForm α := ⟨[C], by simp⟩

def union (D E : DisjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  ⟨D.clauses ++ E.clauses, by simp [D.nonempty]⟩

/-- Distribute `∧` over `∨`: all pairwise merges, row-major order. -/
def distributeConj (D E : DisjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  ⟨pairWith ConjunctiveClause.merge D.clauses E.clauses,
    pairWith_ne_nil D.nonempty E.nonempty⟩

/-- The fusion-closed union of two DNFs. Besides the original clauses from `D` and `E`,
it also includes all pairwise merges between a clause of `D` and a clause of `E`. -/
def closedUnion (D E : DisjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  union (union D E) (distributeConj D E)

@[simp] lemma clauses_singleton (C : ConjunctiveClause α) :
    (singleton C).clauses = [C] := rfl

@[simp] lemma clauses_union (D E : DisjunctiveNormalForm α) :
    (union D E).clauses = D.clauses ++ E.clauses := rfl

@[simp] lemma clauses_distributeConj (D E : DisjunctiveNormalForm α) :
    (distributeConj D E).clauses =
      pairWith ConjunctiveClause.merge D.clauses E.clauses := rfl

lemma mem_union {D E : DisjunctiveNormalForm α} {C : ConjunctiveClause α} :
    C ∈ (union D E).clauses ↔ C ∈ D.clauses ∨ C ∈ E.clauses := List.mem_append

lemma mem_distributeConj {D E : DisjunctiveNormalForm α} {C : ConjunctiveClause α} :
    C ∈ (distributeConj D E).clauses ↔
      ∃ A ∈ D.clauses, ∃ B ∈ E.clauses, ConjunctiveClause.merge A B = C :=
  mem_pairWith (f := ConjunctiveClause.merge) (xs := D.clauses) (ys := E.clauses)

/-- The formula `C₁ ∨ (C₂ ∨ (… ∨ Cₙ))`, in the order of the list. -/
def toFormula (D : DisjunctiveNormalForm α) : Formula α :=
  match h : D.clauses with
  | []      => absurd h D.nonempty
  | C :: Cs => bigDisjCons (ConjunctiveClause.toFormula C)
      (Cs.map ConjunctiveClause.toFormula)

instance : Coe (DisjunctiveNormalForm α) (Formula α) := ⟨toFormula⟩

@[simp] lemma toFormula_singleton (C : ConjunctiveClause α) :
    toFormula (singleton C) = (C : Formula α) := rfl

@[simp] lemma distributeConj_singleton_singleton (C D : ConjunctiveClause α) :
    distributeConj (singleton C) (singleton D) = singleton (ConjunctiveClause.merge C D) := by
  apply ext
  simp [pairWith]

/-- Distribution is commutative up to `≈` (the clause order differs). -/
lemma distributeConj_comm (D E : DisjunctiveNormalForm α) :
    distributeConj D E ≈ distributeConj E D := by
  refine equiv_iff.2 ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨A, hA, B, hB, rfl⟩ := mem_distributeConj.1 hC
    exact ⟨ConjunctiveClause.merge B A, mem_distributeConj.2 ⟨B, hB, A, hA, rfl⟩,
      ConjunctiveClause.merge_comm A B⟩
  · intro C hC
    obtain ⟨B, hB, A, hA, rfl⟩ := mem_distributeConj.1 hC
    exact ⟨ConjunctiveClause.merge A B, mem_distributeConj.2 ⟨A, hA, B, hB, rfl⟩,
      ConjunctiveClause.merge_comm B A⟩

/-- Distribution over a union in the left argument is an equality for lists. -/
lemma distributeConj_union_left (D E F : DisjunctiveNormalForm α) :
    distributeConj (union D E) F =
      union (distributeConj D F) (distributeConj E F) := by
  apply ext
  exact pairWith_append_left ConjunctiveClause.merge D.clauses E.clauses F.clauses

/-- Distribution over a union in the right argument holds up to `≈` (clause order differs). -/
lemma distributeConj_union_right (D E F : DisjunctiveNormalForm α) :
    distributeConj D (union E F) ≈
      union (distributeConj D E) (distributeConj D F) := by
  refine equiv_of_mem_iff fun C => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨A, hA, B, hB, rfl⟩ := mem_distributeConj.1 h
    rcases mem_union.1 hB with hB | hB
    · exact mem_union.2 (Or.inl (mem_distributeConj.2 ⟨A, hA, B, hB, rfl⟩))
    · exact mem_union.2 (Or.inr (mem_distributeConj.2 ⟨A, hA, B, hB, rfl⟩))
  · rcases mem_union.1 h with h | h
    · obtain ⟨A, hA, B, hB, rfl⟩ := mem_distributeConj.1 h
      exact mem_distributeConj.2 ⟨A, hA, B, mem_union.2 (Or.inl hB), rfl⟩
    · obtain ⟨A, hA, B, hB, rfl⟩ := mem_distributeConj.1 h
      exact mem_distributeConj.2 ⟨A, hA, B, mem_union.2 (Or.inr hB), rfl⟩

lemma distributeConj_assoc (D E F : DisjunctiveNormalForm α) :
    distributeConj (distributeConj D E) F ≈
      distributeConj D (distributeConj E F) := by
  refine equiv_iff.2 ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨AB, hAB, c, hc, rfl⟩ := mem_distributeConj.1 hC
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_distributeConj.1 hAB
    exact ⟨ConjunctiveClause.merge a (ConjunctiveClause.merge b c),
      mem_distributeConj.2 ⟨a, ha, ConjunctiveClause.merge b c,
        mem_distributeConj.2 ⟨b, hb, c, hc, rfl⟩, rfl⟩,
      ConjunctiveClause.equiv_of_eq (ConjunctiveClause.merge_assoc a b c)⟩
  · intro C hC
    obtain ⟨a, ha, bc, hbc, rfl⟩ := mem_distributeConj.1 hC
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_distributeConj.1 hbc
    exact ⟨ConjunctiveClause.merge (ConjunctiveClause.merge a b) c,
      mem_distributeConj.2 ⟨ConjunctiveClause.merge a b,
        mem_distributeConj.2 ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩,
      ConjunctiveClause.equiv_of_eq (ConjunctiveClause.merge_assoc a b c).symm⟩

instance [ToString α] : Repr (DisjunctiveNormalForm α) where
  reprPrec D n := Repr.reprPrec (D : Formula α) n

instance [ToString α] : ToString (DisjunctiveNormalForm α) where
  toString D := toString (D : Formula α)

end DisjunctiveNormalForm

namespace ConjunctiveNormalForm

instance : Coe (ConjunctiveNormalForm α) (List (DisjunctiveClause α)) :=
  ⟨ConjunctiveNormalForm.clauses⟩

@[simp] lemma clauses_mk (Γ : List (DisjunctiveClause α)) (h : Γ ≠ []) :
    (ConjunctiveNormalForm.mk Γ h).clauses = Γ := rfl

@[simp] lemma nonempty_coe (C : ConjunctiveNormalForm α) :
    (C : List (DisjunctiveClause α)) ≠ [] := C.nonempty

@[ext] lemma ext {C D : ConjunctiveNormalForm α} (h : C.clauses = D.clauses) : C = D := by
  cases C
  cases D
  cases h
  rfl

@[simp] lemma mem_coe {C : ConjunctiveNormalForm α} {D : DisjunctiveClause α} :
    D ∈ (C : List (DisjunctiveClause α)) ↔ D ∈ C.clauses := Iff.rfl

def singleton (D : DisjunctiveClause α) : ConjunctiveNormalForm α := ⟨[D], by simp⟩

def union (C D : ConjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  ⟨C.clauses ++ D.clauses, by simp [C.nonempty]⟩

/-- Distribute `∨` over `∧`: all pairwise merges, row-major order. -/
def distributeDisj (C D : ConjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  ⟨pairWith DisjunctiveClause.merge C.clauses D.clauses,
    pairWith_ne_nil C.nonempty D.nonempty⟩

/-- The fusion-closed union of two CNFs. Besides the original clauses from `C` and `D`,
it also includes all pairwise merges between a clause of `C` and a clause of `D`. -/
def closedUnion (C D : ConjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  union (union C D) (distributeDisj C D)

@[simp] lemma clauses_singleton (D : DisjunctiveClause α) :
    (singleton D).clauses = [D] := rfl

@[simp] lemma clauses_union (C D : ConjunctiveNormalForm α) :
    (union C D).clauses = C.clauses ++ D.clauses := rfl

@[simp] lemma clauses_distributeDisj (C D : ConjunctiveNormalForm α) :
    (distributeDisj C D).clauses =
      pairWith DisjunctiveClause.merge C.clauses D.clauses := rfl

/-- The formula `D₁ ∧ (D₂ ∧ (… ∧ Dₙ))`, in the order of the list. -/
def toFormula (C : ConjunctiveNormalForm α) : Formula α :=
  match h : C.clauses with
  | []      => absurd h C.nonempty
  | D :: Ds => bigConjCons (DisjunctiveClause.toFormula D)
      (Ds.map DisjunctiveClause.toFormula)

instance : Coe (ConjunctiveNormalForm α) (Formula α) := ⟨toFormula⟩

@[simp] lemma toFormula_singleton (D : DisjunctiveClause α) :
    toFormula (singleton D) = (D : Formula α) := rfl

instance [ToString α] : Repr (ConjunctiveNormalForm α) where
  reprPrec C n := Repr.reprPrec (C : Formula α) n

instance [ToString α] : ToString (ConjunctiveNormalForm α) where
  toString C := toString (C : Formula α)

end ConjunctiveNormalForm

namespace DisjunctiveNormalForm

/-- Complement of a DNF: complement every clause, in the same order. -/
def compl (D : DisjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  ⟨D.clauses.map ConjunctiveClause.compl, by simp [D.nonempty]⟩

@[simp] lemma clauses_compl (D : DisjunctiveNormalForm α) :
    (compl D).clauses = D.clauses.map ConjunctiveClause.compl := rfl

@[simp] lemma compl_singleton (C : ConjunctiveClause α) :
    compl (singleton C) = ConjunctiveNormalForm.singleton (ConjunctiveClause.compl C) := rfl

@[simp] lemma compl_union (D E : DisjunctiveNormalForm α) :
    compl (union D E) = ConjunctiveNormalForm.union (compl D) (compl E) := by
  apply ConjunctiveNormalForm.ext
  simp only [clauses_compl, clauses_union, ConjunctiveNormalForm.clauses_union,
    List.map_append]

@[simp] lemma compl_distributeConj (D E : DisjunctiveNormalForm α) :
    compl (distributeConj D E) =
      ConjunctiveNormalForm.distributeDisj (compl D) (compl E) := by
  apply ConjunctiveNormalForm.ext
  exact map_pairWith
    (f := ConjunctiveClause.merge) (f' := DisjunctiveClause.merge)
    (g := ConjunctiveClause.compl) (g₁ := ConjunctiveClause.compl)
    (g₂ := ConjunctiveClause.compl)
    (fun C C' => ConjunctiveClause.compl_merge C C') D.clauses E.clauses

@[simp] lemma compl_closedUnion (D E : DisjunctiveNormalForm α) :
    compl (closedUnion D E) =
      ConjunctiveNormalForm.closedUnion (compl D) (compl E) := by
  simp [closedUnion, ConjunctiveNormalForm.closedUnion]

/-- Complementing every clause of a list of conjunctive clauses twice is the identity. -/
@[simp] lemma map_compl_map_compl (l : List (ConjunctiveClause α)) :
    (l.map ConjunctiveClause.compl).map DisjunctiveClause.compl = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, ConjunctiveClause.compl_compl, ih]

end DisjunctiveNormalForm

namespace ConjunctiveNormalForm

/-- Complement of a CNF: complement every clause, in the same order. -/
def compl (C : ConjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  ⟨C.clauses.map DisjunctiveClause.compl, by simp [C.nonempty]⟩

@[simp] lemma clauses_compl (C : ConjunctiveNormalForm α) :
    (compl C).clauses = C.clauses.map DisjunctiveClause.compl := rfl

@[simp] lemma compl_singleton (B : DisjunctiveClause α) :
    compl (singleton B) = DisjunctiveNormalForm.singleton (DisjunctiveClause.compl B) := rfl

@[simp] lemma compl_union (C D : ConjunctiveNormalForm α) :
    compl (union C D) = DisjunctiveNormalForm.union (compl C) (compl D) := by
  apply DisjunctiveNormalForm.ext
  simp only [clauses_compl, clauses_union, DisjunctiveNormalForm.clauses_union,
    List.map_append]

@[simp] lemma compl_distributeDisj (C D : ConjunctiveNormalForm α) :
    compl (distributeDisj C D) =
      DisjunctiveNormalForm.distributeConj (compl C) (compl D) := by
  apply DisjunctiveNormalForm.ext
  exact map_pairWith
    (f := DisjunctiveClause.merge) (f' := ConjunctiveClause.merge)
    (g := DisjunctiveClause.compl) (g₁ := DisjunctiveClause.compl)
    (g₂ := DisjunctiveClause.compl)
    (fun C C' => DisjunctiveClause.compl_merge C C') C.clauses D.clauses

@[simp] lemma compl_closedUnion (C D : ConjunctiveNormalForm α) :
    compl (closedUnion C D) =
      DisjunctiveNormalForm.closedUnion (compl C) (compl D) := by
  simp [closedUnion, DisjunctiveNormalForm.closedUnion]

/-- Complementing every clause of a list of disjunctive clauses twice is the identity. -/
@[simp] lemma map_compl_map_compl (l : List (DisjunctiveClause α)) :
    (l.map DisjunctiveClause.compl).map ConjunctiveClause.compl = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, DisjunctiveClause.compl_compl, ih]

@[simp] lemma compl_compl (C : ConjunctiveNormalForm α) :
    DisjunctiveNormalForm.compl (compl C) = C := by
  apply ext
  simp only [DisjunctiveNormalForm.clauses_compl, clauses_compl, map_compl_map_compl]

end ConjunctiveNormalForm

namespace DisjunctiveNormalForm

@[simp] lemma compl_compl (D : DisjunctiveNormalForm α) :
    ConjunctiveNormalForm.compl (compl D) = D := by
  apply ext
  simp only [ConjunctiveNormalForm.clauses_compl, clauses_compl, map_compl_map_compl]

end DisjunctiveNormalForm

/-- Negation normal forms built from literals using conjunction and disjunction. -/
inductive NNF (α : Type u) where
  | lit  : Literal α → NNF α
  | conj : NNF α → NNF α → NNF α
  | disj : NNF α → NNF α → NNF α
  deriving DecidableEq

namespace NNF

variable {α : Type u}

instance : Coe (Literal α) (NNF α) := ⟨lit⟩

/-- The number of nodes in an NNF. -/
def size : NNF α → Nat
  | lit _    => 1
  | conj A B => size A + size B + 1
  | disj A B => size A + size B + 1

/-- The number of disjunction nodes in an NNF. -/
def disjCount : NNF α → Nat
  | lit _    => 0
  | conj A B => disjCount A + disjCount B
  | disj A B => disjCount A + disjCount B + 1

/-- The number of disjunctions that still sit under conjunction-contexts and
therefore have to be distributed away to reach DNF. -/
def dnfDebt : NNF α → Nat
  | lit _    => 0
  | conj A B => dnfDebt A + dnfDebt B + disjCount A + disjCount B
  | disj A B => dnfDebt A + dnfDebt B

/-- A well-founded complexity measure for direct DNF normalization. The `size`
term makes immediate subformulas strictly smaller, while `dnfDebt` tracks the
actual distributive work left to do. -/
def dnfMeasure (A : NNF α) : Nat :=
  size A + dnfDebt A

@[simp] lemma size_lit (ℓ : Literal α) :
    size (lit ℓ : NNF α) = 1 := rfl
@[simp] lemma size_conj (A B : NNF α) :
    size (conj A B : NNF α) = size A + size B + 1 := rfl
@[simp] lemma size_disj (A B : NNF α) :
    size (disj A B : NNF α) = size A + size B + 1 := rfl

@[simp] lemma disjCount_lit (ℓ : Literal α) :
    disjCount (lit ℓ : NNF α) = 0 := rfl
@[simp] lemma disjCount_conj (A B : NNF α) :
    disjCount (conj A B : NNF α) = disjCount A + disjCount B := rfl
@[simp] lemma disjCount_disj (A B : NNF α) :
    disjCount (disj A B : NNF α) = disjCount A + disjCount B + 1 := rfl

@[simp] lemma dnfDebt_lit (ℓ : Literal α) :
    dnfDebt (lit ℓ : NNF α) = 0 := rfl
@[simp] lemma dnfDebt_conj (A B : NNF α) :
    dnfDebt (conj A B : NNF α) = dnfDebt A + dnfDebt B + disjCount A + disjCount B := rfl
@[simp] lemma dnfDebt_disj (A B : NNF α) :
    dnfDebt (disj A B : NNF α) = dnfDebt A + dnfDebt B := rfl

@[simp] lemma dnfMeasure_lit (ℓ : Literal α) :
    dnfMeasure (lit ℓ : NNF α) = 1 := by
  simp [dnfMeasure]
@[simp] lemma dnfMeasure_conj (A B : NNF α) :
    dnfMeasure (conj A B : NNF α) =
      dnfMeasure A + dnfMeasure B + disjCount A + disjCount B + 1 := by
  simp [dnfMeasure, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
@[simp] lemma dnfMeasure_disj (A B : NNF α) :
    dnfMeasure (disj A B : NNF α) =
      dnfMeasure A + dnfMeasure B + 1 := by
  simp [dnfMeasure, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The formula represented by an NNF. -/
def toFormula : NNF α → Formula α
  | lit ℓ    => (ℓ : Formula α)
  | conj A B => toFormula A ∧ toFormula B
  | disj A B => toFormula A ∨ toFormula B

instance : Coe (NNF α) (Formula α) := ⟨toFormula⟩

@[simp] lemma toFormula_lit (ℓ : Literal α) :
    toFormula (lit ℓ : NNF α) = (ℓ : Formula α) := rfl
@[simp] lemma toFormula_conj (A B : NNF α) :
    toFormula (conj A B : NNF α) = ((A : Formula α) ∧ (B : Formula α)) := rfl
@[simp] lemma toFormula_disj (A B : NNF α) :
    toFormula (disj A B : NNF α) = ((A : Formula α) ∨ (B : Formula α)) := rfl

@[simp] lemma coe_coe (A : NNF α) : ((A : Formula α)) = toFormula A := rfl

/-- Pointwise De Morgan complement of an NNF. -/
def compl : NNF α → NNF α
  | lit ℓ    => lit (¯ℓ)
  | conj A B => disj (compl A) (compl B)
  | disj A B => conj (compl A) (compl B)

prefix:max "∼" => compl

@[simp] lemma compl_lit (ℓ : Literal α) :
    compl (lit ℓ : NNF α) = lit (¯ℓ) := rfl

@[simp] lemma compl_conj (A B : NNF α) :
    compl (conj A B : NNF α) = disj (compl A) (compl B) := rfl

@[simp] lemma compl_disj (A B : NNF α) :
    compl (disj A B : NNF α) = conj (compl A) (compl B) := rfl

@[simp] lemma compl_compl (A : NNF α) : compl (compl A) = A := by
  induction A with
  | lit ℓ =>
      simp
  | conj A B hA hB =>
      simp [hA, hB]
  | disj A B hA hB =>
      simp [hA, hB]

instance [ToString α] : Repr (NNF α) where
  reprPrec A n := Repr.reprPrec (A : Formula α) n

instance [ToString α] : ToString (NNF α) where
  toString A := toString (A : Formula α)

/-- Conversion of an NNF to disjunctive normal form. -/
def dnf : NNF α → DisjunctiveNormalForm α
  | lit ℓ    => DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ)
  | conj A B => DisjunctiveNormalForm.distributeConj (dnf A) (dnf B)
  | disj A B => DisjunctiveNormalForm.union (dnf A) (dnf B)

/-- Conversion of an NNF to conjunctive normal form. -/
def cnf : NNF α → ConjunctiveNormalForm α
  | lit ℓ    => ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ)
  | conj A B => ConjunctiveNormalForm.union (cnf A) (cnf B)
  | disj A B => ConjunctiveNormalForm.distributeDisj (cnf A) (cnf B)

/-- Conversion of an NNF to a fusion-closed disjunctive normal form. -/
def closedDnf : NNF α → DisjunctiveNormalForm α
  | lit ℓ    => DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ)
  | conj A B => DisjunctiveNormalForm.distributeConj (closedDnf A) (closedDnf B)
  | disj A B => DisjunctiveNormalForm.closedUnion (closedDnf A) (closedDnf B)

/-- Conversion of an NNF to a fusion-closed conjunctive normal form. -/
def closedCnf : NNF α → ConjunctiveNormalForm α
  | lit ℓ    => ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ)
  | conj A B => ConjunctiveNormalForm.closedUnion (closedCnf A) (closedCnf B)
  | disj A B => ConjunctiveNormalForm.distributeDisj (closedCnf A) (closedCnf B)

@[simp] lemma dnf_lit (ℓ : Literal α) :
    dnf (lit ℓ : NNF α) = DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ) := rfl
@[simp] lemma dnf_conj (A B : NNF α) :
    dnf (conj A B : NNF α) = DisjunctiveNormalForm.distributeConj (dnf A) (dnf B) := rfl
@[simp] lemma dnf_disj (A B : NNF α) :
    dnf (disj A B : NNF α) = DisjunctiveNormalForm.union (dnf A) (dnf B) := rfl

@[simp] lemma cnf_lit (ℓ : Literal α) :
    cnf (lit ℓ : NNF α) = ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ) := rfl
@[simp] lemma cnf_conj (A B : NNF α) :
    cnf (conj A B : NNF α) = ConjunctiveNormalForm.union (cnf A) (cnf B) := rfl
@[simp] lemma cnf_disj (A B : NNF α) :
    cnf (disj A B : NNF α) = ConjunctiveNormalForm.distributeDisj (cnf A) (cnf B) := rfl

@[simp] lemma closedDnf_lit (ℓ : Literal α) :
    closedDnf (lit ℓ : NNF α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ) := rfl
@[simp] lemma closedDnf_conj (A B : NNF α) :
    closedDnf (conj A B : NNF α) =
      DisjunctiveNormalForm.distributeConj (closedDnf A) (closedDnf B) := rfl
@[simp] lemma closedDnf_disj (A B : NNF α) :
    closedDnf (disj A B : NNF α) =
      DisjunctiveNormalForm.closedUnion (closedDnf A) (closedDnf B) := rfl

@[simp] lemma closedCnf_lit (ℓ : Literal α) :
    closedCnf (lit ℓ : NNF α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ) := rfl
@[simp] lemma closedCnf_conj (A B : NNF α) :
    closedCnf (conj A B : NNF α) =
      ConjunctiveNormalForm.closedUnion (closedCnf A) (closedCnf B) := rfl
@[simp] lemma closedCnf_disj (A B : NNF α) :
    closedCnf (disj A B : NNF α) =
      ConjunctiveNormalForm.distributeDisj (closedCnf A) (closedCnf B) := rfl

lemma dnf_mem_closedDnf :
    ∀ {A : NNF α} {C : ConjunctiveClause α},
      C ∈ A.dnf.clauses → C ∈ A.closedDnf.clauses
  | lit ℓ, C, hC => by
      simpa [NNF.dnf, NNF.closedDnf] using hC
  | disj A B, C, hC => by
      rw [NNF.dnf_disj] at hC
      rw [NNF.closedDnf_disj, DisjunctiveNormalForm.closedUnion]
      refine DisjunctiveNormalForm.mem_union.2 (Or.inl ?_)
      refine DisjunctiveNormalForm.mem_union.2 ?_
      rcases DisjunctiveNormalForm.mem_union.1 hC with hA | hB
      · exact Or.inl (dnf_mem_closedDnf hA)
      · exact Or.inr (dnf_mem_closedDnf hB)
  | conj A B, C, hC => by
      rw [NNF.dnf_conj] at hC
      rw [NNF.closedDnf_conj]
      obtain ⟨CA, hA, CB, hB, rfl⟩ := DisjunctiveNormalForm.mem_distributeConj.1 hC
      exact DisjunctiveNormalForm.mem_distributeConj.2
        ⟨CA, dnf_mem_closedDnf hA, CB, dnf_mem_closedDnf hB, rfl⟩

lemma cnf_compl (A : NNF α) :
    cnf (compl A) = DisjunctiveNormalForm.compl (dnf A) := by
  induction A with
  | lit ℓ =>
      simp [NNF.cnf, NNF.dnf]
  | conj A B hA hB =>
      simp [NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, hA, hB]

lemma dnf_compl (A : NNF α) :
    dnf (compl A) = ConjunctiveNormalForm.compl (cnf A) := by
  induction A with
  | lit ℓ =>
      simp [NNF.cnf, NNF.dnf]
  | conj A B hA hB =>
      simp [NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, hA, hB]

lemma closedCnf_compl (A : NNF α) :
    closedCnf (compl A) = DisjunctiveNormalForm.compl (closedDnf A) := by
  induction A with
  | lit ℓ =>
      simp [NNF.closedCnf, NNF.closedDnf]
  | conj A B hA hB =>
      simp [NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, hA, hB]

lemma closedDnf_compl (A : NNF α) :
    closedDnf (compl A) = ConjunctiveNormalForm.compl (closedCnf A) := by
  induction A with
  | lit ℓ =>
      simp [NNF.closedCnf, NNF.closedDnf]
  | conj A B hA hB =>
      simp [NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, hA, hB]

end NNF

variable {α : Type u}

/-- Auxiliary conversion to NNF with a polarity flag. -/
private def nnfAux : Bool → Formula α → NNF α
  | false, var a    => NNF.lit (.pos a)
  | true,  var a    => NNF.lit (.neg a)
  | false, bot      => false
  | false, neg φ    => nnfAux true φ
  | true,  neg φ    => nnfAux false φ
  | false, conj φ ψ => NNF.conj (nnfAux false φ) (nnfAux false ψ)
  | true,  conj φ ψ => NNF.disj (nnfAux true φ) (nnfAux true ψ)
  | false, disj φ ψ => NNF.disj (nnfAux false φ) (nnfAux false ψ)
  | true,  disj φ ψ => NNF.conj (nnfAux true φ) (nnfAux true ψ)

/-- The negation normal form obtained by pushing all negations to the literal level. -/
def nnf (φ : Formula α) : NNF α :=
  nnfAux false φ

/-- The formula obtained by converting `φ` to negation normal form and coercing back to formulas. -/
def nnfToFormula (φ : Formula α) : Formula α :=
  (nnf φ : Formula α)

/-- The disjunctive normal form obtained from `φ` via its negation normal form. -/
def dnf (φ : Formula α) : DisjunctiveNormalForm α :=
  (nnf φ).dnf

/-- The conjunctive normal form obtained from `φ` via its negation normal form. -/
def cnf (φ : Formula α) : ConjunctiveNormalForm α :=
  (nnf φ).cnf

/-- The fusion-closed disjunctive normal form obtained from `φ` via its negation normal form. -/
def closedDnf (φ : Formula α) : DisjunctiveNormalForm α :=
  (nnf φ).closedDnf

/-- The fusion-closed conjunctive normal form obtained from `φ` via its negation normal form. -/
def closedCnf (φ : Formula α) : ConjunctiveNormalForm α :=
  (nnf φ).closedCnf

/-- The formula obtained by converting `φ` to disjunctive normal form and coercing back. -/
def dnfToFormula (φ : Formula α) : Formula α :=
  (dnf φ : Formula α)

/-- The formula obtained by converting `φ` to conjunctive normal form and coercing back. -/
def cnfToFormula (φ : Formula α) : Formula α :=
  (cnf φ : Formula α)

/-- The formula obtained by converting `φ` to fusion-closed disjunctive normal form and coercing back. -/
def closedDnfToFormula (φ : Formula α) : Formula α :=
  (closedDnf φ : Formula α)

/-- The formula obtained by converting `φ` to fusion-closed conjunctive normal form and coercing back. -/
def closedCnfToFormula (φ : Formula α) : Formula α :=
  (closedCnf φ : Formula α)

@[simp] lemma nnf_var (a : α) : nnf (var a : Formula α) = NNF.lit (.pos a) := rfl
@[simp] lemma nnf_neg_var (a : α) : nnf (neg (var a) : Formula α) = NNF.lit (.neg a) := rfl
@[simp] lemma nnf_neg_neg (φ : Formula α) : nnf (neg (neg φ)) = nnf φ := rfl
@[simp] lemma nnf_conj (φ ψ : Formula α) :
    nnf (φ ∧ ψ) = NNF.conj (nnf φ) (nnf ψ) := rfl
@[simp] lemma nnf_disj (φ ψ : Formula α) :
    nnf (φ ∨ ψ) = NNF.disj (nnf φ) (nnf ψ) := rfl
@[simp] lemma nnf_neg_conj (φ ψ : Formula α) :
    nnf (neg (φ ∧ ψ)) = NNF.disj (nnfAux true φ) (nnfAux true ψ) := rfl
@[simp] lemma nnf_neg_disj (φ ψ : Formula α) :
    nnf (neg (φ ∨ ψ)) = NNF.conj (nnfAux true φ) (nnfAux true ψ) := rfl

@[simp] lemma nnfToFormula_eq_coe (φ : Formula α) :
    nnfToFormula φ = (nnf φ : Formula α) := rfl

@[simp] lemma nnfToFormula_var (a : α) :
    nnfToFormula (var a : Formula α) = var a := rfl
@[simp] lemma nnfToFormula_neg_var (a : α) :
    nnfToFormula (neg (var a) : Formula α) = neg (var a) := rfl
@[simp] lemma nnfToFormula_neg_neg (φ : Formula α) :
    nnfToFormula (¬ (¬ φ)) = nnfToFormula φ := rfl
@[simp] lemma nnfToFormula_conj (φ ψ : Formula α) :
    nnfToFormula (φ ∧ ψ) = (nnfToFormula φ ∧ nnfToFormula ψ) := rfl
@[simp] lemma nnfToFormula_disj (φ ψ : Formula α) :
    nnfToFormula (φ ∨ ψ) = (nnfToFormula φ ∨ nnfToFormula ψ) := rfl
@[simp] lemma nnfToFormula_neg_conj (φ ψ : Formula α) :
    nnfToFormula (¬ (φ ∧ ψ)) = (nnfToFormula (¬ φ) ∨ nnfToFormula (¬ ψ)) := rfl
@[simp] lemma nnfToFormula_neg_disj (φ ψ : Formula α) :
    nnfToFormula (¬ (φ ∨ ψ)) = (nnfToFormula (¬ φ) ∧ nnfToFormula (¬ ψ)) := rfl

@[simp] lemma nnfAux_false_of_nnf (A : NNF α) :
    nnfAux false (A : Formula α) = A := by
  induction A with
  | lit ℓ =>
      cases ℓ <;> rfl
  | conj A B hA hB =>
      simp [nnfAux, hA, hB]
  | disj A B hA hB =>
      simp [nnfAux, hA, hB]

@[simp] lemma nnfAux_true_of_nnf (A : NNF α) :
    nnfAux true (A : Formula α) = A.compl := by
  induction A with
  | lit ℓ =>
      cases ℓ <;> rfl
  | conj A B hA hB =>
      simp [nnfAux, NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [nnfAux, NNF.compl, hA, hB]

lemma NNF.toFormula_compl (A : NNF α) :
    (A.compl : Formula α) = nnfToFormula (Formula.neg (A : Formula α)) := by
  induction A with
  | lit ℓ =>
      cases ℓ <;> rfl
  | conj A B hA hB =>
      simp [NNF.compl, nnfToFormula, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, nnfToFormula, hA, hB]

private lemma nnfAux_true_eq_compl_false : ∀ φ : Formula α,
    nnfAux true φ = (nnfAux false φ).compl
  | var a => rfl
  | neg φ => by
      simpa [nnfAux] using (congrArg NNF.compl (nnfAux_true_eq_compl_false φ)).symm
  | conj φ ψ => by
      simp [nnfAux, nnfAux_true_eq_compl_false φ, nnfAux_true_eq_compl_false ψ]
  | disj φ ψ => by
      simp [nnfAux, nnfAux_true_eq_compl_false φ, nnfAux_true_eq_compl_false ψ]

lemma nnf_neg_eq_compl (φ : Formula α) :
    nnf (Formula.neg φ) = (nnf φ).compl := by
  simpa [nnf] using nnfAux_true_eq_compl_false φ

@[simp] lemma dnf_eq_nnf_dnf (φ : Formula α) : dnf φ = (nnf φ).dnf := rfl
@[simp] lemma cnf_eq_nnf_cnf (φ : Formula α) : cnf φ = (nnf φ).cnf := rfl
@[simp] lemma closedDnf_eq_nnf_closedDnf (φ : Formula α) :
    closedDnf φ = (nnf φ).closedDnf := rfl
@[simp] lemma closedCnf_eq_nnf_closedCnf (φ : Formula α) :
    closedCnf φ = (nnf φ).closedCnf := rfl

lemma dnf_mem_closedDnf {φ : Formula α} {C : ConjunctiveClause α}
    (hC : C ∈ (dnf φ).clauses) :
    C ∈ (closedDnf φ).clauses :=
  NNF.dnf_mem_closedDnf hC

lemma cnf_neg_eq_dnf_compl (φ : Formula α) :
    cnf (Formula.neg φ) = DisjunctiveNormalForm.compl (dnf φ) := by
  rw [Formula.cnf, nnf_neg_eq_compl, NNF.cnf_compl, Formula.dnf]

lemma dnf_neg_eq_cnf_compl (φ : Formula α) :
    dnf (Formula.neg φ) = ConjunctiveNormalForm.compl (cnf φ) := by
  rw [Formula.dnf, nnf_neg_eq_compl, NNF.dnf_compl, Formula.cnf]

lemma closedCnf_neg_eq_closedDnf_compl (φ : Formula α) :
    closedCnf (Formula.neg φ) = DisjunctiveNormalForm.compl (closedDnf φ) := by
  rw [Formula.closedCnf, nnf_neg_eq_compl, NNF.closedCnf_compl, Formula.closedDnf]

lemma closedDnf_neg_eq_closedCnf_compl (φ : Formula α) :
    closedDnf (Formula.neg φ) = ConjunctiveNormalForm.compl (closedCnf φ) := by
  rw [Formula.closedDnf, nnf_neg_eq_compl, NNF.closedDnf_compl, Formula.closedCnf]

@[simp] lemma dnf_var (a : α) :
    dnf (var a : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma dnf_neg_var (a : α) :
    dnf (neg (var a) : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.neg a)) := rfl
@[simp] lemma cnf_var (a : α) :
    cnf (var a : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma cnf_neg_var (a : α) :
    cnf (neg (var a) : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.neg a)) := rfl
@[simp] lemma closedDnf_var (a : α) :
    closedDnf (var a : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma closedDnf_neg_var (a : α) :
    closedDnf (neg (var a) : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.neg a)) := rfl
@[simp] lemma closedCnf_var (a : α) :
    closedCnf (var a : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma closedCnf_neg_var (a : α) :
    closedCnf (neg (var a) : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.neg a)) := rfl

@[simp] lemma dnfToFormula_eq_coe (φ : Formula α) :
    dnfToFormula φ = (dnf φ : Formula α) := rfl
@[simp] lemma cnfToFormula_eq_coe (φ : Formula α) :
    cnfToFormula φ = (cnf φ : Formula α) := rfl
@[simp] lemma closedDnfToFormula_eq_coe (φ : Formula α) :
    closedDnfToFormula φ = (closedDnf φ : Formula α) := rfl
@[simp] lemma closedCnfToFormula_eq_coe (φ : Formula α) :
    closedCnfToFormula φ = (closedCnf φ : Formula α) := rfl

lemma cnfToFormula_neg_eq_dnf_compl (φ : Formula α) :
    cnfToFormula (Formula.neg φ) = ((DisjunctiveNormalForm.compl (dnf φ) :
      ConjunctiveNormalForm α) : Formula α) := by
  rw [cnfToFormula, cnf_neg_eq_dnf_compl]

lemma dnfToFormula_neg_eq_cnf_compl (φ : Formula α) :
    dnfToFormula (Formula.neg φ) = ((ConjunctiveNormalForm.compl (cnf φ) :
      DisjunctiveNormalForm α) : Formula α) := by
  rw [dnfToFormula, dnf_neg_eq_cnf_compl]

lemma closedCnfToFormula_neg_eq_closedDnf_compl (φ : Formula α) :
    closedCnfToFormula (Formula.neg φ) = ((DisjunctiveNormalForm.compl (closedDnf φ) :
      ConjunctiveNormalForm α) : Formula α) := by
  rw [closedCnfToFormula, closedCnf_neg_eq_closedDnf_compl]

lemma closedDnfToFormula_neg_eq_closedCnf_compl (φ : Formula α) :
    closedDnfToFormula (Formula.neg φ) = ((ConjunctiveNormalForm.compl (closedCnf φ) :
      DisjunctiveNormalForm α) : Formula α) := by
  rw [closedDnfToFormula, closedDnf_neg_eq_closedCnf_compl]

end Formula
