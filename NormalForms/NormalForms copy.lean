import NormalForms.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic

/-!
# Normal forms for propositional syntax

This file defines separate datatypes for literals and negation normal forms, together
with type synonyms for conjunctive clauses, disjunctive clauses, disjunctive normal
forms, and conjunctive normal forms.

Since the basic syntax has no constants for truth or falsity, conversions of clauses
and normal forms back to formulas are `Option`-valued.
-/

universe u

namespace Formula

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

def sorted (Γ : Finset (Literal α)) [LinearOrder α] : List (Literal α) :=
  Γ.sort (· ≤ ·)

instance [ToString α] : Repr (Literal α) where
  reprPrec ℓ n := Repr.reprPrec (ℓ : Formula α) n

instance [ToString α] : ToString (Literal α) where
  toString ℓ := toString (ℓ : Formula α)

private def toStringFinsetAux [ToString α] [LinearOrder α] (Γ : Finset (Literal α)) : String :=
  "{" ++ String.intercalate ", " ((sorted Γ).map toString) ++ "}"

instance [ToString α] [LinearOrder α] : Repr (Finset (Literal α)) where
  reprPrec Γ _ := toStringFinsetAux Γ

instance [ToString α] [LinearOrder α] : ToString (Finset (Literal α)) where
  toString Γ := toStringFinsetAux Γ

/-- The embedding of literals into formulas. -/
def toFormulaEmbedding : Literal α ↪ Formula α :=
  ⟨toFormula, toFormula_injective⟩

/-- The involutive complementation of literals as an embedding. -/
def complEmbedding : Literal α ↪ Literal α :=
  ⟨compl, fun _ _ h => (compl_inj _ _).1 h⟩

end Literal

/-- A conjunctive clause is a nonempty finite set of literals. -/
structure ConjunctiveClause (α : Type u) where
  lits : List (Literal α)
  nonempty : lits ≠ []
  deriving DecidableEq

/-- A disjunctive clause is a nonempty finite set of literals. -/
structure DisjunctiveClause (α : Type u) where
  lits : Finset (Literal α)
  nonempty : lits.Nonempty
  deriving DecidableEq

namespace ConjunctiveClause

def Equiv (C D : ConjunctiveClause α) : Prop :=
  ∀ ℓ, ℓ ∈ C.lits ↔ ℓ ∈ D.lits

instance setoid : Setoid (ConjunctiveClause α) where
  r := Equiv
  iseqv := ⟨fun _ _ => Iff.rfl, fun h ℓ => (h ℓ).symm, fun h_1 h_2 ℓ => (h_1 ℓ).trans (h_2 ℓ)⟩

instance : Coe (ConjunctiveClause α) (List (Literal α)) := ⟨ConjunctiveClause.lits⟩

/-
def sorted (C : ConjunctiveClause α) [LinearOrder α] : List (Literal α) :=
  Literal.sorted C.lits
-/

@[simp] lemma lits_mk (Γ : List (Literal α)) (h : Γ ≠ []) :
    (ConjunctiveClause.mk Γ h).lits = Γ := rfl

@[simp] lemma nonempty_coe (C : ConjunctiveClause α) :
    (C : List (Literal α)) ≠ [] := C.nonempty

@[ext] lemma ext {C D : ConjunctiveClause α} (h : C.lits = D.lits) : C = D := by
  cases C
  cases D
  cases h
  rfl

/-
lemma sorted_injective [LinearOrder α] :
    Function.Injective (fun C : ConjunctiveClause α => C) := by
  intro C D h
  apply ext
  exact Finset.ext fun ℓ => by
    have hmem : ℓ ∈ sorted C ↔ ℓ ∈ sorted D := by
      simpa using congrArg (fun l : List (Literal α) => ℓ ∈ l) h
    have hC : ℓ ∈ C.lits ↔ ℓ ∈ Literal.sorted C.lits := by
      simp [Literal.sorted]
    have hD : ℓ ∈ D.lits ↔ ℓ ∈ Literal.sorted D.lits := by
      simp [Literal.sorted]
    calc
      ℓ ∈ C.lits ↔ ℓ ∈ sorted C := by simpa [sorted] using hC
      _ ↔ ℓ ∈ sorted D := hmem
      _ ↔ ℓ ∈ D.lits := by simpa [sorted] using hD.symm


instance [LinearOrder α] : LinearOrder (ConjunctiveClause α) :=
  LinearOrder.lift' (fun C => sorted C) sorted_injective
-/


@[simp] lemma mem_coe {C : ConjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (C : List (Literal α)) ↔ ℓ ∈ C.lits :=
  Iff.rfl

def singleton (ℓ : Literal α) : ConjunctiveClause α := ⟨[ℓ], by simp⟩

/-
def merge [DecidableEq α] (C D : ConjunctiveClause α) : ConjunctiveClause α :=
  ⟨C.lits ∪ D.lits,
    C.nonempty.mono (by intro ℓ hℓ; exact Finset.mem_union_left D.lits hℓ)⟩
-/
def merge (C D : ConjunctiveClause α) : ConjunctiveClause α :=
  ⟨C.lits ++ D.lits, by simp [C.nonempty]⟩

@[simp] lemma lits_singleton (ℓ : Literal α) :
    (singleton ℓ).lits = ({ℓ} : List (Literal α)) := rfl

@[simp] lemma lits_merge (C D : ConjunctiveClause α) :
    (merge C D).lits = C.lits ++ D.lits := rfl

@[simp] lemma mem_singleton {ℓ m : Literal α} :
    m ∈ (singleton ℓ : List (Literal α)) ↔ m = ℓ := by
  simp [singleton]

@[simp] lemma mem_merge {C D : ConjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (merge C D : List (Literal α)) ↔ ℓ ∈ C.lits ∨ ℓ ∈ D.lits := by
  simp [merge]

@[simp] lemma merge_comm (C D : ConjunctiveClause α) :
    merge C D ≈ merge D C := by
  intro ℓ
  simp [merge, List.mem_append, or_comm]

@[simp] lemma merge_assoc (C D E : ConjunctiveClause α) :
    merge (merge C D) E = merge C (merge D E) := by
  ext1
  simp [merge, List.append_assoc]

@[simp] lemma merge_idem (C : ConjunctiveClause α) :
    merge C C ≈ C := by
  change Equiv _ _
  intro ℓ
  simp [merge]

@[simp] lemma merge_absorb_distrib
    (C D E : ConjunctiveClause α) :
    merge (merge C D) (merge C E) ≈ merge C (merge D E) := by
  intro ℓ
  simp [or_left_comm]

/-
Hier nog congruence lemmas?
-/

def toFormula (C : ConjunctiveClause α) : Formula α :=
  match h : C.lits with
  | []      => absurd h C.nonempty
  | ℓ :: ls => bigConjCons ℓ.toFormula (ls.map Literal.toFormula)

instance [LinearOrder α] : Coe (ConjunctiveClause α) (Formula α) := ⟨toFormula⟩

@[simp] lemma coe_coe [LinearOrder α] (C : ConjunctiveClause α) :
    ((C : Formula α)) = toFormula C := rfl

@[simp] lemma toFormula_mk (ℓ : Literal α) (ls : List (Literal α)) (h : ℓ :: ls ≠ []) :
    toFormula ⟨ℓ :: ls, h⟩ =
      bigConjCons ℓ.toFormula (ls.map Literal.toFormula) := rfl

@[simp] lemma toFormula_singleton (ℓ : Literal α) :
    toFormula (singleton ℓ) = (ℓ : Formula α) := by
  simp [singleton, toFormula, Formula.bigConjCons]

instance [ToString α] [LinearOrder α] : Repr (ConjunctiveClause α) where
  reprPrec C n := Repr.reprPrec (C : Formula α) n

instance [ToString α] [LinearOrder α] : ToString (ConjunctiveClause α) where
  toString C := toString (C : Formula α)

end ConjunctiveClause

namespace DisjunctiveClause

instance : Coe (DisjunctiveClause α) (Finset (Literal α)) := ⟨DisjunctiveClause.lits⟩

def sorted (C : DisjunctiveClause α) [LinearOrder α] : List (Literal α) :=
  Literal.sorted C.lits

@[simp] lemma lits_mk (Γ : Finset (Literal α)) (h : Γ.Nonempty) :
    (DisjunctiveClause.mk Γ h).lits = Γ := rfl

@[simp] lemma nonempty_coe (C : DisjunctiveClause α) :
    (C : Finset (Literal α)).Nonempty := C.nonempty

@[ext] lemma ext {C D : DisjunctiveClause α} (h : C.lits = D.lits) : C = D := by
  cases C
  cases D
  cases h
  rfl

lemma sorted_injective [LinearOrder α] :
    Function.Injective (fun C : DisjunctiveClause α => sorted C) := by
  intro C D h
  apply ext
  exact Finset.ext fun ℓ => by
    have hmem : ℓ ∈ sorted C ↔ ℓ ∈ sorted D := by
      simpa using congrArg (fun l : List (Literal α) => ℓ ∈ l) h
    have hC : ℓ ∈ C.lits ↔ ℓ ∈ Literal.sorted C.lits := by
      simp [Literal.sorted]
    have hD : ℓ ∈ D.lits ↔ ℓ ∈ Literal.sorted D.lits := by
      simp [Literal.sorted]
    calc
      ℓ ∈ C.lits ↔ ℓ ∈ sorted C := by simpa [sorted] using hC
      _ ↔ ℓ ∈ sorted D := hmem
      _ ↔ ℓ ∈ D.lits := by simpa [sorted] using hD.symm

instance [LinearOrder α] : LinearOrder (DisjunctiveClause α) :=
  LinearOrder.lift' (fun C => sorted C) sorted_injective

@[simp] lemma mem_coe {C : DisjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (C : Finset (Literal α)) ↔ ℓ ∈ C.lits :=
  Iff.rfl

def singleton (ℓ : Literal α) : DisjunctiveClause α := ⟨{ℓ}, by simp⟩

def merge [DecidableEq α] (C D : DisjunctiveClause α) : DisjunctiveClause α :=
  ⟨C.lits ∪ D.lits,
    C.nonempty.mono (by intro ℓ hℓ; exact Finset.mem_union_left D.lits hℓ)⟩

@[simp] lemma lits_singleton (ℓ : Literal α) :
    (singleton ℓ).lits = ({ℓ} : Finset (Literal α)) := rfl

@[simp] lemma lits_merge [DecidableEq α] (C D : DisjunctiveClause α) :
    (merge C D).lits = C.lits ∪ D.lits := rfl

@[simp] lemma mem_singleton {ℓ m : Literal α} :
    m ∈ (singleton ℓ : Finset (Literal α)) ↔ m = ℓ := by
  simp [singleton]

@[simp] lemma mem_merge [DecidableEq α] {C D : DisjunctiveClause α} {ℓ : Literal α} :
    ℓ ∈ (merge C D : Finset (Literal α)) ↔ ℓ ∈ C.lits ∨ ℓ ∈ D.lits := by
  simp [merge]

def toFormula [LinearOrder α] (C : DisjunctiveClause α) : Formula α :=
  Formula.bigDisjFinsetNE
    (Γ := C.lits.image Literal.toFormulaEmbedding)
    (by
      rcases C.nonempty with ⟨ℓ, hℓ⟩
      refine ⟨ℓ.toFormula, ?_⟩
      exact Finset.mem_image.2 ⟨ℓ, hℓ, rfl⟩)

instance [LinearOrder α] : Coe (DisjunctiveClause α) (Formula α) := ⟨toFormula⟩

@[simp] lemma coe_coe [LinearOrder α] (C : DisjunctiveClause α) :
    ((C : Formula α)) = toFormula C := rfl

@[simp] lemma toFormula_mk [LinearOrder α] (Γ : Finset (Literal α)) (h : Γ.Nonempty) :
    toFormula ⟨Γ, h⟩ =
      Formula.bigDisjFinsetNE
        (Γ := Γ.image Literal.toFormulaEmbedding)
        (by
          rcases h with ⟨ℓ, hℓ⟩
          exact ⟨ℓ.toFormula, Finset.mem_image.2 ⟨ℓ, hℓ, rfl⟩⟩) := rfl

@[simp] lemma toFormula_singleton [LinearOrder α] (ℓ : Literal α) :
    toFormula (singleton ℓ) = (ℓ : Formula α) := by
  simp [singleton, toFormula, Formula.bigDisjFinsetNE, Literal.toFormulaEmbedding]

instance [ToString α] [LinearOrder α] : Repr (DisjunctiveClause α) where
  reprPrec C n := Repr.reprPrec (C : Formula α) n

instance [ToString α] [LinearOrder α] : ToString (DisjunctiveClause α) where
  toString C := toString (C : Formula α)

end DisjunctiveClause

namespace ConjunctiveClause

def compl [DecidableEq α] (C : ConjunctiveClause α) : DisjunctiveClause α :=
  ⟨C.lits.image Formula.Literal.complEmbedding,
    by
      rcases C.nonempty with ⟨ℓ, hℓ⟩
      exact ⟨¯ℓ, Finset.mem_image.2 ⟨ℓ, hℓ, rfl⟩⟩⟩

@[simp] lemma lits_compl [DecidableEq α] (C : ConjunctiveClause α) :
    (compl C).lits = C.lits.image Formula.Literal.complEmbedding := rfl

@[simp] lemma compl_singleton [DecidableEq α] (ℓ : Literal α) :
    compl (singleton ℓ) = DisjunctiveClause.singleton (¯ℓ) := by
  ext m
  simp [compl, singleton, Formula.Literal.complEmbedding]

@[simp] lemma compl_merge [DecidableEq α] (C D : ConjunctiveClause α) :
    compl (merge C D) = DisjunctiveClause.merge (compl C) (compl D) := by
  ext ℓ
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨m, hm, rfl⟩
    rcases Finset.mem_union.1 hm with hm | hm
    · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_image.2 ⟨m, hm, rfl⟩
    · exact Finset.mem_union.2 <| Or.inr <| Finset.mem_image.2 ⟨m, hm, rfl⟩
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_image.1 h with ⟨m, hm, rfl⟩
      exact Finset.mem_image.2 ⟨m, Finset.mem_union.2 (Or.inl hm), rfl⟩
    · rcases Finset.mem_image.1 h with ⟨m, hm, rfl⟩
      exact Finset.mem_image.2 ⟨m, Finset.mem_union.2 (Or.inr hm), rfl⟩

end ConjunctiveClause

namespace DisjunctiveClause

def compl [DecidableEq α] (C : DisjunctiveClause α) : ConjunctiveClause α :=
  ⟨C.lits.image Formula.Literal.complEmbedding,
    by
      rcases C.nonempty with ⟨ℓ, hℓ⟩
      exact ⟨¯ℓ, Finset.mem_image.2 ⟨ℓ, hℓ, rfl⟩⟩⟩

@[simp] lemma lits_compl [DecidableEq α] (C : DisjunctiveClause α) :
    (compl C).lits = C.lits.image Formula.Literal.complEmbedding := rfl

@[simp] lemma compl_singleton [DecidableEq α] (ℓ : Literal α) :
    compl (singleton ℓ) = ConjunctiveClause.singleton (¯ℓ) := by
  ext m
  simp [compl, singleton, Formula.Literal.complEmbedding]

@[simp] lemma compl_merge [DecidableEq α] (C D : DisjunctiveClause α) :
    compl (merge C D) = ConjunctiveClause.merge (compl C) (compl D) := by
  ext ℓ
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨m, hm, rfl⟩
    rcases Finset.mem_union.1 hm with hm | hm
    · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_image.2 ⟨m, hm, rfl⟩
    · exact Finset.mem_union.2 <| Or.inr <| Finset.mem_image.2 ⟨m, hm, rfl⟩
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_image.1 h with ⟨m, hm, rfl⟩
      exact Finset.mem_image.2 ⟨m, Finset.mem_union.2 (Or.inl hm), rfl⟩
    · rcases Finset.mem_image.1 h with ⟨m, hm, rfl⟩
      exact Finset.mem_image.2 ⟨m, Finset.mem_union.2 (Or.inr hm), rfl⟩

@[simp] lemma compl_compl [DecidableEq α] (C : DisjunctiveClause α) :
    ConjunctiveClause.compl (compl C) = C := by
  ext ℓ
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨m, hm, hmEq⟩
    rcases Finset.mem_image.1 hm with ⟨n, hn, hnEq⟩
    subst hmEq hnEq
    simpa [Formula.Literal.complEmbedding] using hn
  · intro h
    exact Finset.mem_image.2
      ⟨¯ℓ, Finset.mem_image.2 ⟨ℓ, h, by simp [Formula.Literal.complEmbedding]⟩,
        by simp [Formula.Literal.complEmbedding]⟩

def complEmbedding [DecidableEq α] : DisjunctiveClause α ↪ ConjunctiveClause α :=
  ⟨compl, fun _ _ h => by
    have h' := congrArg ConjunctiveClause.compl h
    simpa using h'⟩

end DisjunctiveClause

namespace ConjunctiveClause

@[simp] lemma compl_compl [DecidableEq α] (C : ConjunctiveClause α) :
    DisjunctiveClause.compl (compl C) = C := by
  ext ℓ
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨m, hm, hmEq⟩
    rcases Finset.mem_image.1 hm with ⟨n, hn, hnEq⟩
    subst hmEq hnEq
    simpa [Formula.Literal.complEmbedding] using hn
  · intro h
    exact Finset.mem_image.2
      ⟨¯ℓ, Finset.mem_image.2 ⟨ℓ, h, by simp [Formula.Literal.complEmbedding]⟩,
        by simp [Formula.Literal.complEmbedding]⟩

def complEmbedding [DecidableEq α] : ConjunctiveClause α ↪ DisjunctiveClause α :=
  ⟨compl, fun _ _ h => by
    have h' := congrArg DisjunctiveClause.compl h
    simpa using h'⟩

end ConjunctiveClause

/-- A disjunctive normal form is a nonempty finite set of conjunctive clauses. -/
structure DisjunctiveNormalForm (α : Type u) where
  clauses : Finset (ConjunctiveClause α)
  nonempty : clauses.Nonempty
  deriving DecidableEq

/-- A conjunctive normal form is a nonempty finite set of disjunctive clauses. -/
structure ConjunctiveNormalForm (α : Type u) where
  clauses : Finset (DisjunctiveClause α)
  nonempty : clauses.Nonempty
  deriving DecidableEq

abbrev DNF (α : Type u) := DisjunctiveNormalForm α
abbrev CNF (α : Type u) := ConjunctiveNormalForm α

namespace DisjunctiveNormalForm

instance : Coe (DisjunctiveNormalForm α) (Finset (ConjunctiveClause α)) :=
  ⟨DisjunctiveNormalForm.clauses⟩

@[simp] lemma clauses_mk (Γ : Finset (ConjunctiveClause α)) (h : Γ.Nonempty) :
    (DisjunctiveNormalForm.mk Γ h).clauses = Γ := rfl

@[simp] lemma nonempty_coe (D : DisjunctiveNormalForm α) :
    (D : Finset (ConjunctiveClause α)).Nonempty := D.nonempty

@[ext] lemma ext {D E : DisjunctiveNormalForm α} (h : D.clauses = E.clauses) : D = E := by
  cases D
  cases E
  cases h
  rfl

@[simp] lemma mem_coe {D : DisjunctiveNormalForm α} {C : ConjunctiveClause α} :
    C ∈ (D : Finset (ConjunctiveClause α)) ↔ C ∈ D.clauses := Iff.rfl

def singleton (C : ConjunctiveClause α) : DisjunctiveNormalForm α := ⟨{C}, by simp⟩

def union [DecidableEq α] (D E : DisjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  ⟨D.clauses ∪ E.clauses,
    D.nonempty.mono (by intro C hC; exact Finset.mem_union_left E.clauses hC)⟩

def distributeConj [DecidableEq α] (D E : DisjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  ⟨Finset.image₂ ConjunctiveClause.merge D.clauses E.clauses,
    by
      rcases D.nonempty with ⟨C, hC⟩
      rcases E.nonempty with ⟨C', hC'⟩
      exact ⟨ConjunctiveClause.merge C C', Finset.mem_image₂.2 ⟨C, hC, C', hC', rfl⟩⟩⟩

/-- The fusion-closed union of two DNFs. Besides the original clauses from `D` and `E`,
it also includes all pairwise merges between a clause of `D` and a clause of `E`. -/
def closedUnion [DecidableEq α] (D E : DisjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  union (union D E) (distributeConj D E)

def toFormula [LinearOrder α] (D : DisjunctiveNormalForm α) : Formula α :=
  Formula.bigDisjFinsetNE
    (Γ := D.clauses.image (fun C : ConjunctiveClause α => (C : Formula α)))
    (by
      rcases D.nonempty with ⟨C, hC⟩
      exact ⟨(C : Formula α), Finset.mem_image.2 ⟨C, hC, rfl⟩⟩)

instance [LinearOrder α] : Coe (DisjunctiveNormalForm α) (Formula α) := ⟨toFormula⟩

@[simp] lemma toFormula_singleton [LinearOrder α] (C : ConjunctiveClause α) :
    toFormula (singleton C) = (C : Formula α) := by
  rw [toFormula]
  simp [singleton, Formula.bigDisjFinsetNE]

@[simp] lemma distributeConj_singleton_singleton [DecidableEq α]
    (C D : ConjunctiveClause α) :
    distributeConj (singleton C) (singleton D) = singleton (ConjunctiveClause.merge C D) := by
  ext E
  constructor
  · intro hE
    rcases Finset.mem_image₂.1 hE with ⟨C', hC', D', hD', hEq⟩
    have hC'' : C' = C := by simpa [singleton] using hC'
    have hD'' : D' = D := by simpa [singleton] using hD'
    subst hC'' hD''
    simpa [singleton] using hEq.symm
  · intro hE
    have hEq : E = ConjunctiveClause.merge C D := by simpa [singleton] using hE
    subst hEq
    exact Finset.mem_image₂.2 ⟨C, by simpa [singleton], D, by simpa [singleton], rfl⟩

@[simp] lemma distributeConj_comm [DecidableEq α]
    (D E : DisjunctiveNormalForm α) :
    distributeConj D E = distributeConj E D := by
  ext C
  constructor
  · intro hC
    rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, hEq⟩
    exact Finset.mem_image₂.2 ⟨C₂, h₂, C₁, h₁, by simpa [ConjunctiveClause.merge_comm] using hEq⟩
  · intro hC
    rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, hEq⟩
    exact Finset.mem_image₂.2 ⟨C₂, h₂, C₁, h₁, by simpa [ConjunctiveClause.merge_comm] using hEq⟩

@[simp] lemma distributeConj_union_left [DecidableEq α]
    (D E F : DisjunctiveNormalForm α) :
    distributeConj (union D E) F =
      union (distributeConj D F) (distributeConj E F) := by
  ext C
  constructor
  · intro hC
    rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, rfl⟩
    rcases Finset.mem_union.1 h₁ with h₁ | h₁
    · exact Finset.mem_union.2 <| Or.inl <|
        Finset.mem_image₂.2 ⟨C₁, h₁, C₂, h₂, rfl⟩
    · exact Finset.mem_union.2 <| Or.inr <|
        Finset.mem_image₂.2 ⟨C₁, h₁, C₂, h₂, rfl⟩
  · intro hC
    rcases Finset.mem_union.1 hC with hC | hC
    · rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, rfl⟩
      exact Finset.mem_image₂.2 ⟨C₁, Finset.mem_union.2 (Or.inl h₁), C₂, h₂, rfl⟩
    · rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, rfl⟩
      exact Finset.mem_image₂.2 ⟨C₁, Finset.mem_union.2 (Or.inr h₁), C₂, h₂, rfl⟩

@[simp] lemma distributeConj_union_right [DecidableEq α]
    (D E F : DisjunctiveNormalForm α) :
    distributeConj D (union E F) =
      union (distributeConj D E) (distributeConj D F) := by
  ext C
  constructor
  · intro hC
    rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, rfl⟩
    rcases Finset.mem_union.1 h₂ with h₂ | h₂
    · exact Finset.mem_union.2 <| Or.inl <|
        Finset.mem_image₂.2 ⟨C₁, h₁, C₂, h₂, rfl⟩
    · exact Finset.mem_union.2 <| Or.inr <|
        Finset.mem_image₂.2 ⟨C₁, h₁, C₂, h₂, rfl⟩
  · intro hC
    rcases Finset.mem_union.1 hC with hC | hC
    · rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, rfl⟩
      exact Finset.mem_image₂.2 ⟨C₁, h₁, C₂, Finset.mem_union.2 (Or.inl h₂), rfl⟩
    · rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, rfl⟩
      exact Finset.mem_image₂.2 ⟨C₁, h₁, C₂, Finset.mem_union.2 (Or.inr h₂), rfl⟩

@[simp] lemma distributeConj_assoc [DecidableEq α]
    (D E F : DisjunctiveNormalForm α) :
    distributeConj (distributeConj D E) F =
      distributeConj D (distributeConj E F) := by
  ext C
  constructor
  · intro hC
    rcases Finset.mem_image₂.1 hC with ⟨CD, hCD, E', hE', rfl⟩
    rcases Finset.mem_image₂.1 hCD with ⟨C', hC', D', hD', rfl⟩
    exact Finset.mem_image₂.2
      ⟨C', hC', ConjunctiveClause.merge D' E',
        Finset.mem_image₂.2 ⟨D', hD', E', hE', rfl⟩,
        by simpa using (ConjunctiveClause.merge_assoc C' D' E').symm⟩
  · intro hC
    rcases Finset.mem_image₂.1 hC with ⟨C', hC', DE, hDE, rfl⟩
    rcases Finset.mem_image₂.1 hDE with ⟨D', hD', E', hE', rfl⟩
    exact Finset.mem_image₂.2
      ⟨ConjunctiveClause.merge C' D',
        Finset.mem_image₂.2 ⟨C', hC', D', hD', rfl⟩,
        E', hE',
        by simpa using ConjunctiveClause.merge_assoc C' D' E'⟩

instance [ToString α] [LinearOrder α] : Repr (DisjunctiveNormalForm α) where
  reprPrec D n := Repr.reprPrec (D : Formula α) n

instance [ToString α] [LinearOrder α] : ToString (DisjunctiveNormalForm α) where
  toString D := toString (D : Formula α)

end DisjunctiveNormalForm

namespace ConjunctiveNormalForm

instance : Coe (ConjunctiveNormalForm α) (Finset (DisjunctiveClause α)) :=
  ⟨ConjunctiveNormalForm.clauses⟩

@[simp] lemma clauses_mk (Γ : Finset (DisjunctiveClause α)) (h : Γ.Nonempty) :
    (ConjunctiveNormalForm.mk Γ h).clauses = Γ := rfl

@[simp] lemma nonempty_coe (C : ConjunctiveNormalForm α) :
    (C : Finset (DisjunctiveClause α)).Nonempty := C.nonempty

@[ext] lemma ext {C D : ConjunctiveNormalForm α} (h : C.clauses = D.clauses) : C = D := by
  cases C
  cases D
  cases h
  rfl

@[simp] lemma mem_coe {C : ConjunctiveNormalForm α} {D : DisjunctiveClause α} :
    D ∈ (C : Finset (DisjunctiveClause α)) ↔ D ∈ C.clauses := Iff.rfl

def singleton (D : DisjunctiveClause α) : ConjunctiveNormalForm α := ⟨{D}, by simp⟩

def union [DecidableEq α] (C D : ConjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  ⟨C.clauses ∪ D.clauses,
    C.nonempty.mono (by intro B hB; exact Finset.mem_union_left D.clauses hB)⟩

def distributeDisj [DecidableEq α] (C D : ConjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  ⟨Finset.image₂ DisjunctiveClause.merge C.clauses D.clauses,
    by
      rcases C.nonempty with ⟨B, hB⟩
      rcases D.nonempty with ⟨B', hB'⟩
      exact ⟨DisjunctiveClause.merge B B', Finset.mem_image₂.2 ⟨B, hB, B', hB', rfl⟩⟩⟩

/-- The fusion-closed union of two CNFs. Besides the original clauses from `C` and `D`,
it also includes all pairwise merges between a clause of `C` and a clause of `D`. -/
def closedUnion [DecidableEq α] (C D : ConjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  union (union C D) (distributeDisj C D)

def toFormula [LinearOrder α] (C : ConjunctiveNormalForm α) : Formula α :=
  Formula.bigConjFinsetNE
    (Γ := C.clauses.image (fun D : DisjunctiveClause α => (D : Formula α)))
    (by
      rcases C.nonempty with ⟨D, hD⟩
      exact ⟨(D : Formula α), Finset.mem_image.2 ⟨D, hD, rfl⟩⟩)

instance [LinearOrder α] : Coe (ConjunctiveNormalForm α) (Formula α) := ⟨toFormula⟩

@[simp] lemma toFormula_singleton [LinearOrder α] (D : DisjunctiveClause α) :
    toFormula (singleton D) = (D : Formula α) := by
  rw [toFormula]
  simp [singleton, Formula.bigConjFinsetNE]

instance [ToString α] [LinearOrder α] : Repr (ConjunctiveNormalForm α) where
  reprPrec C n := Repr.reprPrec (C : Formula α) n

instance [ToString α] [LinearOrder α] : ToString (ConjunctiveNormalForm α) where
  toString C := toString (C : Formula α)

end ConjunctiveNormalForm

namespace DisjunctiveNormalForm

def compl [DecidableEq α] (D : DisjunctiveNormalForm α) : ConjunctiveNormalForm α :=
  ⟨D.clauses.image ConjunctiveClause.complEmbedding,
    by
      rcases D.nonempty with ⟨C, hC⟩
      exact ⟨ConjunctiveClause.compl C, Finset.mem_image.2 ⟨C, hC, rfl⟩⟩⟩

@[simp] lemma clauses_compl [DecidableEq α] (D : DisjunctiveNormalForm α) :
    (compl D).clauses = D.clauses.image ConjunctiveClause.complEmbedding := rfl

@[simp] lemma compl_singleton [DecidableEq α] (C : ConjunctiveClause α) :
    compl (singleton C) = ConjunctiveNormalForm.singleton (ConjunctiveClause.compl C) := by
  ext B
  simp [DisjunctiveNormalForm.compl, DisjunctiveNormalForm.singleton,
    ConjunctiveNormalForm.singleton, ConjunctiveClause.complEmbedding]

@[simp] lemma compl_union [DecidableEq α] (D E : DisjunctiveNormalForm α) :
    compl (union D E) = ConjunctiveNormalForm.union (compl D) (compl E) := by
  ext B
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨C, hC, rfl⟩
    rcases Finset.mem_union.1 hC with hC | hC
    · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_image.2 ⟨C, hC, rfl⟩
    · exact Finset.mem_union.2 <| Or.inr <| Finset.mem_image.2 ⟨C, hC, rfl⟩
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_image.1 h with ⟨C, hC, rfl⟩
      exact Finset.mem_image.2 ⟨C, Finset.mem_union.2 (Or.inl hC), rfl⟩
    · rcases Finset.mem_image.1 h with ⟨C, hC, rfl⟩
      exact Finset.mem_image.2 ⟨C, Finset.mem_union.2 (Or.inr hC), rfl⟩

@[simp] lemma compl_distributeConj [DecidableEq α]
    (D E : DisjunctiveNormalForm α) :
    compl (distributeConj D E) = ConjunctiveNormalForm.distributeDisj (compl D) (compl E) := by
  ext B
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨C, hC, hBC⟩
    rcases Finset.mem_image₂.1 hC with ⟨C₁, h₁, C₂, h₂, hEq⟩
    subst hEq
    refine Finset.mem_image₂.2 ?_
    refine ⟨ConjunctiveClause.compl C₁, Finset.mem_image.2 ⟨C₁, h₁, rfl⟩,
      ConjunctiveClause.compl C₂, Finset.mem_image.2 ⟨C₂, h₂, rfl⟩, ?_⟩
    simpa [ConjunctiveClause.complEmbedding] using hBC
  · intro h
    rcases Finset.mem_image₂.1 h with ⟨B₁, h₁, B₂, h₂, hEq⟩
    rcases Finset.mem_image.1 h₁ with ⟨C₁, hC₁, rfl⟩
    rcases Finset.mem_image.1 h₂ with ⟨C₂, hC₂, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨ConjunctiveClause.merge C₁ C₂,
      Finset.mem_image₂.2 ⟨C₁, hC₁, C₂, hC₂, rfl⟩, ?_⟩
    simpa [ConjunctiveClause.complEmbedding] using hEq

end DisjunctiveNormalForm

namespace ConjunctiveNormalForm

def compl [DecidableEq α] (C : ConjunctiveNormalForm α) : DisjunctiveNormalForm α :=
  ⟨C.clauses.image DisjunctiveClause.complEmbedding,
    by
      rcases C.nonempty with ⟨B, hB⟩
      exact ⟨DisjunctiveClause.compl B, Finset.mem_image.2 ⟨B, hB, rfl⟩⟩⟩

@[simp] lemma clauses_compl [DecidableEq α] (C : ConjunctiveNormalForm α) :
    (compl C).clauses = C.clauses.image DisjunctiveClause.complEmbedding := rfl

@[simp] lemma compl_singleton [DecidableEq α] (B : DisjunctiveClause α) :
    compl (singleton B) = DisjunctiveNormalForm.singleton (DisjunctiveClause.compl B) := by
  ext D
  simp [ConjunctiveNormalForm.compl, ConjunctiveNormalForm.singleton,
    DisjunctiveNormalForm.singleton, DisjunctiveClause.complEmbedding]

@[simp] lemma compl_union [DecidableEq α] (C D : ConjunctiveNormalForm α) :
    compl (union C D) = DisjunctiveNormalForm.union (compl C) (compl D) := by
  ext B
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨C, hC, rfl⟩
    rcases Finset.mem_union.1 hC with hC | hC
    · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_image.2 ⟨C, hC, rfl⟩
    · exact Finset.mem_union.2 <| Or.inr <| Finset.mem_image.2 ⟨C, hC, rfl⟩
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_image.1 h with ⟨C, hC, rfl⟩
      exact Finset.mem_image.2 ⟨C, Finset.mem_union.2 (Or.inl hC), rfl⟩
    · rcases Finset.mem_image.1 h with ⟨C, hC, rfl⟩
      exact Finset.mem_image.2 ⟨C, Finset.mem_union.2 (Or.inr hC), rfl⟩

@[simp] lemma compl_distributeDisj [DecidableEq α]
    (C D : ConjunctiveNormalForm α) :
    compl (distributeDisj C D) = DisjunctiveNormalForm.distributeConj (compl C) (compl D) := by
  ext B
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨C', hC', hBC⟩
    rcases Finset.mem_image₂.1 hC' with ⟨C₁, h₁, C₂, h₂, hEq⟩
    subst hEq
    refine Finset.mem_image₂.2 ?_
    refine ⟨DisjunctiveClause.compl C₁, Finset.mem_image.2 ⟨C₁, h₁, rfl⟩,
      DisjunctiveClause.compl C₂, Finset.mem_image.2 ⟨C₂, h₂, rfl⟩, ?_⟩
    simpa [DisjunctiveClause.complEmbedding] using hBC
  · intro h
    rcases Finset.mem_image₂.1 h with ⟨B₁, h₁, B₂, h₂, hEq⟩
    rcases Finset.mem_image.1 h₁ with ⟨C₁, hC₁, rfl⟩
    rcases Finset.mem_image.1 h₂ with ⟨C₂, hC₂, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨DisjunctiveClause.merge C₁ C₂,
      Finset.mem_image₂.2 ⟨C₁, hC₁, C₂, hC₂, rfl⟩, ?_⟩
    simpa [DisjunctiveClause.complEmbedding] using hEq

@[simp] lemma compl_compl [DecidableEq α] (C : ConjunctiveNormalForm α) :
    DisjunctiveNormalForm.compl (compl C) = C := by
  ext B
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨D, hD, hEq⟩
    rcases Finset.mem_image.1 hD with ⟨B', hB', hEq'⟩
    have hBB' : B = B' := by
      calc
        B = ConjunctiveClause.compl D := by
              simpa [ConjunctiveClause.complEmbedding] using hEq.symm
        _ = ConjunctiveClause.compl (DisjunctiveClause.compl B') := by
              simpa [DisjunctiveClause.complEmbedding] using (congrArg ConjunctiveClause.compl hEq').symm
        _ = B' := by simp
    subst hBB'
    exact hB'
  · intro h
    exact Finset.mem_image.2
      ⟨DisjunctiveClause.compl B, Finset.mem_image.2 ⟨B, h, rfl⟩,
        by simp [ConjunctiveClause.complEmbedding]⟩

end ConjunctiveNormalForm

namespace DisjunctiveNormalForm

@[simp] lemma compl_compl [DecidableEq α] (D : DisjunctiveNormalForm α) :
    ConjunctiveNormalForm.compl (compl D) = D := by
  ext C
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨B, hB, hEq⟩
    rcases Finset.mem_image.1 hB with ⟨C', hC', hEq'⟩
    have hCeq : C = C' := by
      calc
        C = DisjunctiveClause.compl B := by
              simpa [DisjunctiveClause.complEmbedding] using hEq.symm
        _ = DisjunctiveClause.compl (ConjunctiveClause.compl C') := by
              simpa [ConjunctiveClause.complEmbedding] using (congrArg DisjunctiveClause.compl hEq').symm
        _ = C' := by simp
    subst hCeq
    exact hC'
  · intro h
    exact Finset.mem_image.2
      ⟨ConjunctiveClause.compl C, Finset.mem_image.2 ⟨C, h, rfl⟩,
        by simp [DisjunctiveClause.complEmbedding]⟩

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
def dnf [DecidableEq α] : NNF α → DisjunctiveNormalForm α
  | lit ℓ    => DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ)
  | conj A B => DisjunctiveNormalForm.distributeConj (dnf A) (dnf B)
  | disj A B => DisjunctiveNormalForm.union (dnf A) (dnf B)

/-- Conversion of an NNF to conjunctive normal form. -/
def cnf [DecidableEq α] : NNF α → ConjunctiveNormalForm α
  | lit ℓ    => ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ)
  | conj A B => ConjunctiveNormalForm.union (cnf A) (cnf B)
  | disj A B => ConjunctiveNormalForm.distributeDisj (cnf A) (cnf B)

/-- Conversion of an NNF to a fusion-closed disjunctive normal form. -/
def closedDnf [DecidableEq α] : NNF α → DisjunctiveNormalForm α
  | lit ℓ    => DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ)
  | conj A B => DisjunctiveNormalForm.distributeConj (closedDnf A) (closedDnf B)
  | disj A B => DisjunctiveNormalForm.closedUnion (closedDnf A) (closedDnf B)

/-- Conversion of an NNF to a fusion-closed conjunctive normal form. -/
def closedCnf [DecidableEq α] : NNF α → ConjunctiveNormalForm α
  | lit ℓ    => ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ)
  | conj A B => ConjunctiveNormalForm.closedUnion (closedCnf A) (closedCnf B)
  | disj A B => ConjunctiveNormalForm.distributeDisj (closedCnf A) (closedCnf B)

@[simp] lemma dnf_lit [DecidableEq α] (ℓ : Literal α) :
    dnf (lit ℓ : NNF α) = DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ) := rfl
@[simp] lemma dnf_conj [DecidableEq α] (A B : NNF α) :
    dnf (conj A B : NNF α) = DisjunctiveNormalForm.distributeConj (dnf A) (dnf B) := rfl
@[simp] lemma dnf_disj [DecidableEq α] (A B : NNF α) :
    dnf (disj A B : NNF α) = DisjunctiveNormalForm.union (dnf A) (dnf B) := rfl

@[simp] lemma cnf_lit [DecidableEq α] (ℓ : Literal α) :
    cnf (lit ℓ : NNF α) = ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ) := rfl
@[simp] lemma cnf_conj [DecidableEq α] (A B : NNF α) :
    cnf (conj A B : NNF α) = ConjunctiveNormalForm.union (cnf A) (cnf B) := rfl
@[simp] lemma cnf_disj [DecidableEq α] (A B : NNF α) :
    cnf (disj A B : NNF α) = ConjunctiveNormalForm.distributeDisj (cnf A) (cnf B) := rfl

@[simp] lemma closedDnf_lit [DecidableEq α] (ℓ : Literal α) :
    closedDnf (lit ℓ : NNF α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton ℓ) := rfl
@[simp] lemma closedDnf_conj [DecidableEq α] (A B : NNF α) :
    closedDnf (conj A B : NNF α) =
      DisjunctiveNormalForm.distributeConj (closedDnf A) (closedDnf B) := rfl
@[simp] lemma closedDnf_disj [DecidableEq α] (A B : NNF α) :
    closedDnf (disj A B : NNF α) =
      DisjunctiveNormalForm.closedUnion (closedDnf A) (closedDnf B) := rfl

@[simp] lemma closedCnf_lit [DecidableEq α] (ℓ : Literal α) :
    closedCnf (lit ℓ : NNF α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton ℓ) := rfl
@[simp] lemma closedCnf_conj [DecidableEq α] (A B : NNF α) :
    closedCnf (conj A B : NNF α) =
      ConjunctiveNormalForm.closedUnion (closedCnf A) (closedCnf B) := rfl
@[simp] lemma closedCnf_disj [DecidableEq α] (A B : NNF α) :
    closedCnf (disj A B : NNF α) =
      ConjunctiveNormalForm.distributeDisj (closedCnf A) (closedCnf B) := rfl

lemma dnf_mem_closedDnf [DecidableEq α] :
    ∀ {A : NNF α} {C : ConjunctiveClause α},
      C ∈ A.dnf.clauses → C ∈ A.closedDnf.clauses
  | lit ℓ, C, hC => by
      simpa [NNF.dnf, NNF.closedDnf] using hC
  | disj A B, C, hC => by
      rw [NNF.dnf_disj] at hC
      rw [NNF.closedDnf_disj, DisjunctiveNormalForm.closedUnion]
      exact Finset.mem_union.2 <| Or.inl <|
        (Finset.mem_union.2 <| (Finset.mem_union.1 hC).elim
          (fun hA => Or.inl (dnf_mem_closedDnf hA))
          (fun hB => Or.inr (dnf_mem_closedDnf hB)))
  | conj A B, C, hC => by
      simp [NNF.dnf_conj, NNF.closedDnf_conj] at hC ⊢
      rcases Finset.mem_image₂.1 hC with ⟨CA, hA, CB, hB, rfl⟩
      exact Finset.mem_image₂.2
        ⟨CA, dnf_mem_closedDnf hA, CB, dnf_mem_closedDnf hB, rfl⟩

lemma cnf_compl [DecidableEq α] (A : NNF α) :
    cnf (compl A) = DisjunctiveNormalForm.compl (dnf A) := by
  induction A with
  | lit ℓ =>
      simp [NNF.cnf, NNF.dnf]
  | conj A B hA hB =>
      simp [NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, hA, hB]

lemma dnf_compl [DecidableEq α] (A : NNF α) :
    dnf (compl A) = ConjunctiveNormalForm.compl (cnf A) := by
  induction A with
  | lit ℓ =>
      simp [NNF.cnf, NNF.dnf]
  | conj A B hA hB =>
      simp [NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, hA, hB]

@[simp] lemma DisjunctiveNormalForm.compl_closedUnion [DecidableEq α]
    (D E : DisjunctiveNormalForm α) :
    DisjunctiveNormalForm.compl (DisjunctiveNormalForm.closedUnion D E) =
      ConjunctiveNormalForm.closedUnion
        (DisjunctiveNormalForm.compl D) (DisjunctiveNormalForm.compl E) := by
  simp [DisjunctiveNormalForm.closedUnion, ConjunctiveNormalForm.closedUnion]

@[simp] lemma ConjunctiveNormalForm.compl_closedUnion [DecidableEq α]
    (C D : ConjunctiveNormalForm α) :
    ConjunctiveNormalForm.compl (ConjunctiveNormalForm.closedUnion C D) =
      DisjunctiveNormalForm.closedUnion
        (ConjunctiveNormalForm.compl C) (ConjunctiveNormalForm.compl D) := by
  simp [ConjunctiveNormalForm.closedUnion, DisjunctiveNormalForm.closedUnion]

lemma closedCnf_compl [DecidableEq α] (A : NNF α) :
    closedCnf (compl A) = DisjunctiveNormalForm.compl (closedDnf A) := by
  induction A with
  | lit ℓ =>
      simp [NNF.closedCnf, NNF.closedDnf]
  | conj A B hA hB =>
      simp [NNF.compl, hA, hB]
  | disj A B hA hB =>
      simp [NNF.compl, hA, hB]

lemma closedDnf_compl [DecidableEq α] (A : NNF α) :
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
def dnf [DecidableEq α] (φ : Formula α) : DisjunctiveNormalForm α :=
  (nnf φ).dnf

/-- The conjunctive normal form obtained from `φ` via its negation normal form. -/
def cnf [DecidableEq α] (φ : Formula α) : ConjunctiveNormalForm α :=
  (nnf φ).cnf

/-- The fusion-closed disjunctive normal form obtained from `φ` via its negation normal form. -/
def closedDnf [DecidableEq α] (φ : Formula α) : DisjunctiveNormalForm α :=
  (nnf φ).closedDnf

/-- The fusion-closed conjunctive normal form obtained from `φ` via its negation normal form. -/
def closedCnf [DecidableEq α] (φ : Formula α) : ConjunctiveNormalForm α :=
  (nnf φ).closedCnf

/-- The formula obtained by converting `φ` to disjunctive normal form and coercing back. -/
def dnfToFormula [DecidableEq α] [LinearOrder α] (φ : Formula α) : Formula α :=
  (dnf φ : Formula α)

/-- The formula obtained by converting `φ` to conjunctive normal form and coercing back. -/
def cnfToFormula [DecidableEq α] [LinearOrder α] (φ : Formula α) : Formula α :=
  (cnf φ : Formula α)

/-- The formula obtained by converting `φ` to fusion-closed disjunctive normal form and coercing back. -/
def closedDnfToFormula [DecidableEq α] [LinearOrder α] (φ : Formula α) : Formula α :=
  (closedDnf φ : Formula α)

/-- The formula obtained by converting `φ` to fusion-closed conjunctive normal form and coercing back. -/
def closedCnfToFormula [DecidableEq α] [LinearOrder α] (φ : Formula α) : Formula α :=
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

@[simp] lemma dnf_eq_nnf_dnf [DecidableEq α] (φ : Formula α) : dnf φ = (nnf φ).dnf := rfl
@[simp] lemma cnf_eq_nnf_cnf [DecidableEq α] (φ : Formula α) : cnf φ = (nnf φ).cnf := rfl
@[simp] lemma closedDnf_eq_nnf_closedDnf [DecidableEq α] (φ : Formula α) :
    closedDnf φ = (nnf φ).closedDnf := rfl
@[simp] lemma closedCnf_eq_nnf_closedCnf [DecidableEq α] (φ : Formula α) :
    closedCnf φ = (nnf φ).closedCnf := rfl

lemma dnf_mem_closedDnf [DecidableEq α] {φ : Formula α} {C : ConjunctiveClause α}
    (hC : C ∈ (dnf φ).clauses) :
    C ∈ (closedDnf φ).clauses :=
  NNF.dnf_mem_closedDnf hC

lemma cnf_neg_eq_dnf_compl [DecidableEq α] (φ : Formula α) :
    cnf (Formula.neg φ) = DisjunctiveNormalForm.compl (dnf φ) := by
  rw [Formula.cnf, nnf_neg_eq_compl, NNF.cnf_compl, Formula.dnf]

lemma dnf_neg_eq_cnf_compl [DecidableEq α] (φ : Formula α) :
    dnf (Formula.neg φ) = ConjunctiveNormalForm.compl (cnf φ) := by
  rw [Formula.dnf, nnf_neg_eq_compl, NNF.dnf_compl, Formula.cnf]

lemma closedCnf_neg_eq_closedDnf_compl [DecidableEq α] (φ : Formula α) :
    closedCnf (Formula.neg φ) = DisjunctiveNormalForm.compl (closedDnf φ) := by
  rw [Formula.closedCnf, nnf_neg_eq_compl, NNF.closedCnf_compl, Formula.closedDnf]

lemma closedDnf_neg_eq_closedCnf_compl [DecidableEq α] (φ : Formula α) :
    closedDnf (Formula.neg φ) = ConjunctiveNormalForm.compl (closedCnf φ) := by
  rw [Formula.closedDnf, nnf_neg_eq_compl, NNF.closedDnf_compl, Formula.closedCnf]

@[simp] lemma dnf_var [DecidableEq α] (a : α) :
    dnf (var a : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma dnf_neg_var [DecidableEq α] (a : α) :
    dnf (neg (var a) : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.neg a)) := rfl
@[simp] lemma cnf_var [DecidableEq α] (a : α) :
    cnf (var a : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma cnf_neg_var [DecidableEq α] (a : α) :
    cnf (neg (var a) : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.neg a)) := rfl
@[simp] lemma closedDnf_var [DecidableEq α] (a : α) :
    closedDnf (var a : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma closedDnf_neg_var [DecidableEq α] (a : α) :
    closedDnf (neg (var a) : Formula α) =
      DisjunctiveNormalForm.singleton (ConjunctiveClause.singleton (.neg a)) := rfl
@[simp] lemma closedCnf_var [DecidableEq α] (a : α) :
    closedCnf (var a : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.pos a)) := rfl
@[simp] lemma closedCnf_neg_var [DecidableEq α] (a : α) :
    closedCnf (neg (var a) : Formula α) =
      ConjunctiveNormalForm.singleton (DisjunctiveClause.singleton (.neg a)) := rfl

@[simp] lemma dnfToFormula_eq_coe [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    dnfToFormula φ = (dnf φ : Formula α) := rfl
@[simp] lemma cnfToFormula_eq_coe [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    cnfToFormula φ = (cnf φ : Formula α) := rfl
@[simp] lemma closedDnfToFormula_eq_coe [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    closedDnfToFormula φ = (closedDnf φ : Formula α) := rfl
@[simp] lemma closedCnfToFormula_eq_coe [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    closedCnfToFormula φ = (closedCnf φ : Formula α) := rfl

lemma cnfToFormula_neg_eq_dnf_compl [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    cnfToFormula (Formula.neg φ) = ((DisjunctiveNormalForm.compl (dnf φ) :
      ConjunctiveNormalForm α) : Formula α) := by
  rw [cnfToFormula, cnf_neg_eq_dnf_compl]

lemma dnfToFormula_neg_eq_cnf_compl [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    dnfToFormula (Formula.neg φ) = ((ConjunctiveNormalForm.compl (cnf φ) :
      DisjunctiveNormalForm α) : Formula α) := by
  rw [dnfToFormula, dnf_neg_eq_cnf_compl]

lemma closedCnfToFormula_neg_eq_closedDnf_compl [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    closedCnfToFormula (Formula.neg φ) = ((DisjunctiveNormalForm.compl (closedDnf φ) :
      ConjunctiveNormalForm α) : Formula α) := by
  rw [closedCnfToFormula, closedCnf_neg_eq_closedDnf_compl]

lemma closedDnfToFormula_neg_eq_closedCnf_compl [DecidableEq α] [LinearOrder α] (φ : Formula α) :
    closedDnfToFormula (Formula.neg φ) = ((ConjunctiveNormalForm.compl (closedCnf φ) :
      DisjunctiveNormalForm α) : Formula α) := by
  rw [closedDnfToFormula, closedDnf_neg_eq_closedCnf_compl]
end Formula
