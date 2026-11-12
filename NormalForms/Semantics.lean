import NormalForms.Basic
import NormalForms.NormalForms_tussentype
set_option linter.style.longLine false

universe u

abbrev Val (α : Type u) := α → Bool

namespace Val

variable {α : Type u}

def eval : Formula α → Val α → Bool
  | Formula.var i, v    => v i
  | Formula.neg φ , v   => !(eval φ v)
  | Formula.conj φ ψ, v => ((eval φ v) && (eval ψ v))
  | Formula.disj φ ψ, v => (eval φ v) || (eval ψ v)
  | Formula.imp φ ψ, v  => !(eval φ v) || (eval ψ v)
  | Formula.iff φ ψ, v  => (eval φ v) == (eval ψ v)


instance : CoeFun (Val α) (fun _ => Formula α → Bool) where
  coe v ϕ := eval ϕ v

notation "⟦" ϕ " , " v "⟧" => eval ϕ v

@[simp]
lemma bivalence_one (v : Val α) (ϕ : Formula α) :
    ⟦ ϕ , v ⟧ ≠ true → ⟦ ϕ , v ⟧ = false := by
      grind

@[simp]
lemma bivalence_two (v : Val α) (ϕ : Formula α) :
    ⟦ ϕ , v ⟧ ≠ false → ⟦ ϕ , v ⟧ = true := by
      grind

@[simp]
lemma neg_true (ϕ : Formula α) (v : Val α) :
    ⟦¬ϕ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) := by
  simp [eval]

@[simp]
lemma neg_false (ϕ : Formula α) (v : Val α) :
    ⟦¬ϕ , v⟧ = false ↔ (⟦ϕ , v⟧ = true) := by
  simp [eval]

@[simp]
lemma conj_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∧ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∧ (⟦ψ , v⟧ = true) := by
  simp only [eval]
  simp only [Bool.and_eq_true_iff]

@[simp]
lemma conj_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∧ ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = false) ∨ (⟦ψ , v⟧ = false) := by
      simp only [eval]
      simp only [Bool.and_eq_false_iff]

@[simp]
lemma disj_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∨ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∨ (⟦ψ , v⟧ = true) := by
  simp only [eval]
  simp only [Bool.or_eq_true_iff]

@[simp]
lemma disj_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∨ ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = false) ∧ (⟦ψ , v⟧ = false) := by
  simp only [eval]
  simp only [Bool.or_eq_false_iff]

@[simp]
lemma imp_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ → ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) ∨ (⟦ψ , v⟧ = true) := by
  simp [eval]

@[simp]
lemma imp_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ → ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = true) ∧ (⟦ψ , v⟧ = false) := by
  simp [eval]

@[simp]
lemma iff_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ↔ ψ , v⟧ = true ↔ ((⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = true)) := by
  simp [eval]

@[simp]
lemma iff_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ↔ ψ , v⟧ = false ↔ ((⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = false)) := by
  by_cases hϕ : ⟦ϕ , v⟧ = true
  · by_cases hψ : ⟦ψ , v⟧ = true
    · simp [eval, hϕ, hψ]
    · simp [eval, hϕ, hψ]
  · by_cases hψ : ⟦ψ , v⟧ = true
    · simp [eval, hϕ, hψ]
    · simp [eval, hϕ, hψ]
    /- Explanation:
      The proof uses case analysis on the truth values of ⟦ϕ , v⟧ and ⟦ψ , v⟧.
      There are four possible combinations of truth values (true/false) for ϕ and ψ.
      In each case, we simplify the expression ⟦ϕ ↔ ψ , v⟧ using the definition of evaluation and the known truth values,
      which leads to the desired equivalence.
    -/


end Val

def Sat {α : Type u} (Γ : Set (Formula α)) : Prop :=
  ∃ v : Val α, (∀ψ ∈ Γ, ⟦ψ , v⟧ = true)

namespace Sat

variable {α : Type u}

@[simp]
lemma truth_monotone {v : Val α} {Γ Δ : Set (Formula α)} (h : Γ ⊆ Δ) (g : ∀ ψ ∈ Δ, ⟦ψ , v⟧ = true) :
    ∀ψ ∈  Γ, ⟦ψ , v ⟧ = true := by
      grind

@[simp]
lemma not_sat_iff_some_false (Γ : Set (Formula α)) : ¬ Sat Γ ↔ ∀ v : Val α, ∃ ψ ∈ Γ, ⟦ψ , v⟧ = false := by
  simp[Sat]


@[simp]
lemma sat_monotone {Γ Δ : Set (Formula α)} (h : Sat Δ) (g : Γ ⊆ Δ) : Sat Γ := by
   simp only [Sat] at h
   obtain ⟨v, hv⟩ := h
   simp only [Sat]
   apply Exists.intro v
   apply truth_monotone g
   trivial

end Sat

-- # Logical Consequence

def Consequence {α : Type u} (Γ : Set (Formula α)) (ϕ : Formula α) : Prop :=
  ∀ v : Val α, (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true)

notation Γ " ⊨ " ϕ => Consequence Γ ϕ
notation Γ " ⊭ " ϕ => ¬ Consequence Γ ϕ

namespace Consequence

variable {α : Type u}

@[simp]
lemma def_iff {Γ : Set (Formula α)} {ϕ : Formula α} :
    (Γ ⊨ ϕ) ↔ (∀ v : Val α, (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true)) := by
  rfl

@[simp]
lemma consequence_iff_not_sat {Γ : Set (Formula α)} :
  ∀ ϕ : Formula α, (Γ ⊨ ϕ) ↔ ¬ Sat (Γ ∪ {¬ϕ}) := by
    simp[Sat]
    grind

@[simp]
lemma non_consequence_iff_sat {Γ : Set (Formula α)} (ϕ : Formula α) :
  (Γ ⊭ ϕ) ↔ Sat (Γ ∪ {¬ϕ}) := by
    simp[Sat]
    grind

@[simp]
lemma refl {Γ : Set (Formula α)} {ϕ : Formula α} (mem : ϕ ∈ Γ) : (Γ ⊨ ϕ) := by
  simp
  grind


@[simp]
lemma monotonicity {Γ Δ : Set (Formula α)} {ϕ : Formula α}
    (h : Γ ⊨ ϕ) (g : Γ ⊆ Δ) : (Δ ⊨ ϕ) := by
    simp at h g
    simp
    grind

@[simp]
lemma trans {Γ Δ : Set (Formula α)} {ϕ : Formula α} (h : Γ ⊨ ϕ) : ((Γ ∪ Δ) ⊨ ϕ) := by
  simp at h
  simp
  grind

@[simp]
lemma conj_intro {Γ Δ : Set (Formula α)} {ϕ ψ : Formula α}
    (h : Γ ⊨ ϕ) (g : Δ ⊨ ψ) : ((Γ ∪ Δ) ⊨ ϕ ∧ ψ) := by
      simp at h g
      simp
      grind

@[simp]
lemma conj_elim_left {Γ : Set (Formula α)} {ϕ ψ : Formula α} (h : Γ ⊨ ϕ ∧ ψ) :
    (Γ ⊨ ϕ):= by
      simp at h
      simp
      grind

@[simp]
lemma conj_elim_right {Γ : Set (Formula α)} {ϕ ψ : Formula α} (h : Γ ⊨ ϕ ∧ ψ) :
    (Γ ⊨ ψ):= by
      simp at h
      simp
      grind

@[simp]
lemma disj_intro_left {Γ : Set (Formula α)} {ϕ ψ : Formula α}
  (h : Γ ⊨ ϕ) : (Γ ⊨ ϕ ∨ ψ) := by
    simp at h
    simp
    grind

@[simp]
lemma disj_intro_right {Γ : Set (Formula α)} {ϕ ψ : Formula α}
  (h : Γ ⊨ ψ) : (Γ ⊨ ϕ ∨ ψ) := by
    simp at h
    simp
    grind

@[simp]
lemma disj_elim {Γ Δ Ξ : Set (Formula α)} {ϕ ψ χ : Formula α}
  (h : Γ ⊨ (ϕ ∨ ψ)) (g : (Δ ∪ {ϕ}) ⊨ χ) (f : (Ξ ∪ {ψ}) ⊨ χ) : ((Γ ∪ Δ ∪ Ξ) ⊨ χ) := by
    simp at h g f
    simp
    grind

@[simp]
lemma imp_intro {Γ : Set (Formula α)} {ϕ ψ : Formula α}
    (h : (Γ ∪ {ϕ}) ⊨ ψ) : (Γ ⊨ ϕ → ψ) := by
      simp at h
      simp[Val.eval]
      grind

@[simp]
lemma imp_elim {Γ Δ : Set (Formula α)} {ϕ ψ : Formula α} (h : Γ ⊨ ϕ → ψ) (g : Δ ⊨ ϕ) :
    (Γ ∪ Δ ) ⊨ ψ := by
      simp[Val.eval] at h g
      simp
      grind

end Consequence

def Valid {α : Type u} (ϕ : Formula α) : Prop :=
  ∅ ⊨ ϕ

notation "⊨ " ϕ => Valid ϕ

namespace Valid

variable {α : Type u}

@[simp]
lemma valid_iff {ϕ : Formula α} :
    (⊨ ϕ) ↔  ∀ v : Val α, ⟦ϕ , v⟧ = true := by
      simp[Valid, Consequence.def_iff]

@[simp]
lemma bivalid_iff {ϕ : Formula α} :
    (⊨ ϕ) ↔ ¬ Sat {¬ϕ} := by
      simp[Valid]

@[simp]
lemma law_of_excluded_middle (ϕ : Formula α) :
    ⊨ ϕ ∨ ¬ϕ := by
      simp[Valid]

@[simp]
lemma law_of_non_contradiction (ϕ : Formula α) :
    ⊨ ¬(ϕ ∧ ¬ϕ) := by
      simp[Valid]

end Valid

def Eqv {α : Type u} (ϕ ψ : Formula α) : Prop :=
  ⊨ (ϕ ↔ ψ)

notation ϕ " ⟚ " ψ => Eqv ϕ ψ

namespace Eqv

variable {α : Type u}

@[simp]
lemma equivalence_to_implication (ϕ ψ : Formula α) :
    (ϕ ⟚ ψ) ↔ (⊨ (ϕ → ψ)) ∧ (⊨ (ψ → ϕ)) := by
      simp[Eqv, Valid.valid_iff]
      grind

@[simp]
lemma refl (ϕ : Formula α) : ϕ ⟚ ϕ := by
  simp[Eqv]

@[simp]
lemma symm {ϕ ψ : Formula α} (h : ϕ ⟚ ψ) : ψ ⟚ ϕ := by
  simp[Eqv] at h
  simp[Eqv]
  grind

@[simp]
lemma iff_negation {ϕ ψ : Formula α} (h : ϕ ⟚ ψ) : (¬ϕ) ⟚ (¬ψ) := by
  simp[Eqv] at h
  simp[Eqv]
  grind

@[simp]
lemma iff_conjunction {ϕ₁ ϕ₂ ψ₁ ψ₂ : Formula α}
  (h₁ : ϕ₁ ⟚ ψ₁) (h₂ : ϕ₂ ⟚ ψ₂) : (ϕ₁ ∧ ϕ₂) ⟚ (ψ₁ ∧ ψ₂) := by
    simp[Eqv] at h₁ h₂
    simp[Eqv]
    grind

end Eqv
