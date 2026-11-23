import NormalForms.Basic
import Mathlib.Data.Set.Basic
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
      intro h
      rewrite [Bool.eq_false_iff]
      exact h

@[simp]
lemma bivalence_two (v : Val α) (ϕ : Formula α) :
    ⟦ ϕ , v ⟧ ≠ false → ⟦ ϕ , v ⟧ = true := by
      intro h
      cases h' : ⟦ ϕ , v ⟧ with
      | true => rfl
      | false =>
        exfalso
        exact h h'

@[simp]
lemma neg_true (ϕ : Formula α) (v : Val α) :
    ⟦¬ϕ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) := by
      constructor
      · intro h
        have hneq : ⟦ϕ , v⟧ ≠ true := by
          intro h'
          have hneg : ⟦¬ϕ , v⟧ = false := by
            rw [show ⟦¬ϕ , v⟧ = !(⟦ϕ , v⟧) by rfl, h']
            rfl
          have : (false : Bool) = true := by
            calc
              false = ⟦¬ϕ , v⟧ := hneg.symm
              _ = true := h
          cases this
        exact bivalence_one v ϕ hneq
      · intro hfalse
        rw [show ⟦¬ϕ , v⟧ = !(⟦ϕ , v⟧) by rfl, hfalse]
        rfl

@[simp]
lemma neg_false (ϕ : Formula α) (v : Val α) :
    ⟦¬ϕ , v⟧ = false ↔ (⟦ϕ , v⟧ = true) := by
      constructor
      · intro h
        have hneq : ⟦ϕ , v⟧ ≠ false := by
          intro h'
          have hneg : ⟦¬ϕ , v⟧ = true := by
            rw [show ⟦¬ϕ , v⟧ = !(⟦ϕ , v⟧) by rfl, h']
            rfl
          have : (true : Bool) = false := by
            calc
              true = ⟦¬ϕ , v⟧ := hneg.symm
              _ = false := h
          cases this
        exact bivalence_two v ϕ hneq
      · intro htrue
        rw [show ⟦¬ϕ , v⟧ = !(⟦ϕ , v⟧) by rfl, htrue]
        rfl

@[simp]
lemma conj_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∧ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∧ (⟦ψ , v⟧ = true) := by
      constructor
      · intro h
        have hϕ : ⟦ϕ , v⟧ = true := by
          rw [show ⟦ϕ ∧ ψ , v⟧ = (⟦ϕ , v⟧ && ⟦ψ , v⟧) by rfl] at h
          rw [Bool.and_eq_true_iff] at h
          exact h.1
        have hψ : ⟦ψ , v⟧ = true := by
          rw [show ⟦ϕ ∧ ψ , v⟧ = (⟦ϕ , v⟧ && ⟦ψ , v⟧) by rfl] at h
          rw [Bool.and_eq_true_iff] at h
          exact h.2
        exact ⟨hϕ, hψ⟩
      · intro h
        rw [show ⟦ϕ ∧ ψ , v⟧ = (⟦ϕ , v⟧ && ⟦ψ , v⟧) by rfl]
        exact Bool.and_eq_true_iff.mpr h

@[simp]
lemma conj_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∧ ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = false) ∨ (⟦ψ , v⟧ = false) := by
      constructor
      · intro h
        rw [show ⟦ϕ ∧ ψ , v⟧ = (⟦ϕ , v⟧ && ⟦ψ , v⟧) by rfl] at h
        rw [Bool.and_eq_false_iff] at h
        exact h
      · intro h
        rw [show ⟦ϕ ∧ ψ , v⟧ = (⟦ϕ , v⟧ && ⟦ψ , v⟧) by rfl]
        exact Bool.and_eq_false_iff.mpr h

@[simp]
lemma disj_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∨ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∨ (⟦ψ , v⟧ = true) := by
      constructor
      · intro h
        rw [show ⟦ϕ ∨ ψ , v⟧ = (⟦ϕ , v⟧ || ⟦ψ , v⟧) by rfl] at h
        rw [Bool.or_eq_true_iff] at h
        exact h
      · intro h
        rw [show ⟦ϕ ∨ ψ , v⟧ = (⟦ϕ , v⟧ || ⟦ψ , v⟧) by rfl]
        exact Bool.or_eq_true_iff.mpr h

@[simp]
lemma disj_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ∨ ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = false) ∧ (⟦ψ , v⟧ = false) := by
      constructor
      · intro h
        rw [show ⟦ϕ ∨ ψ , v⟧ = (⟦ϕ , v⟧ || ⟦ψ , v⟧) by rfl] at h
        rw [Bool.or_eq_false_iff] at h
        exact h
      · intro h
        rw [show ⟦ϕ ∨ ψ , v⟧ = (⟦ϕ , v⟧ || ⟦ψ , v⟧) by rfl]
        exact Bool.or_eq_false_iff.mpr h

@[simp]
lemma imp_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ → ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) ∨ (⟦ψ , v⟧ = true) := by
      constructor
      · intro h
        rw [show ⟦ϕ → ψ , v⟧ = (!(⟦ϕ , v⟧) || (⟦ψ , v⟧)) by rfl] at h
        rw [Bool.or_eq_true_iff] at h
        rw [Bool.not_eq_true'] at h
        exact h
      · intro h
        rw [show ⟦ϕ → ψ , v⟧ = (!(⟦ϕ , v⟧) || (⟦ψ , v⟧)) by rfl]
        rw [Bool.or_eq_true_iff]
        rw [Bool.not_eq_true']
        exact h

@[simp]
lemma imp_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ → ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = true) ∧ (⟦ψ , v⟧ = false) := by
      constructor
      · intro h
        rw [show ⟦ϕ → ψ , v⟧ = (!(⟦ϕ , v⟧) || (⟦ψ , v⟧)) by rfl] at h
        rw [Bool.or_eq_false_iff] at h
        rw [Bool.not_eq_false'] at h
        exact h
      · intro h
        rw [show ⟦ϕ → ψ , v⟧ = (!(⟦ϕ , v⟧) || (⟦ψ , v⟧)) by rfl]
        rw [Bool.or_eq_false_iff]
        rw [Bool.not_eq_false']
        exact h

@[simp]
lemma iff_true (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ↔ ψ , v⟧ = true ↔ ((⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = true)) := by
      rw [show ⟦ϕ ↔ ψ , v⟧ = (⟦ϕ , v⟧ == ⟦ψ , v⟧) by rfl]
      cases hϕ : ⟦ϕ , v⟧ <;> cases hψ : ⟦ψ , v⟧
      · constructor
        · intro _
          rfl
        · intro _
          rfl
      · constructor
        · intro h
          cases h
        · intro h
          exact h.2 rfl
      · constructor
        · intro h
          cases h
        · intro h
          exact h.1 rfl
      · constructor
        · intro _
          rfl
        · intro _
          rfl

@[simp]
lemma iff_false (ϕ ψ : Formula α) (v : Val α) :
    ⟦ϕ ↔ ψ , v⟧ = false ↔ ((⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = false)) := by
      rw [show ⟦ϕ ↔ ψ , v⟧ = (⟦ϕ , v⟧ == ⟦ψ , v⟧) by rfl]
      cases hϕ : ⟦ϕ , v⟧ <;> cases hψ : ⟦ψ , v⟧
      · constructor
        · intro h
          cases h
        · intro h
          cases h.mpr rfl
      · constructor
        · intro _
          constructor
          · intro h
            cases h
          · intro h
            cases h
        · intro _
          rfl
      · constructor
        · intro _
          constructor
          · intro _
            rfl
          · intro _
            rfl
        · intro _
          rfl
      · constructor
        · intro h
          cases h
        · intro h
          exact h.1 rfl

end Val

def Sat {α : Type u} (Γ : Set (Formula α)) : Prop :=
  ∃ v : Val α, (∀ψ ∈ Γ, ⟦ψ , v⟧ = true)

namespace Sat

variable {α : Type u}

@[simp]
lemma truth_monotone {v : Val α} {Γ Δ : Set (Formula α)} (h : Γ ⊆ Δ) (g : ∀ ψ ∈ Δ, ⟦ψ , v⟧ = true) :
    ∀ψ ∈  Γ, ⟦ψ , v ⟧ = true := by
      rw [Set.subset_def] at h
      intro ψ hψ
      have hψ' : ψ ∈ Δ := h ψ hψ
      exact g ψ hψ'

@[simp]
lemma not_sat_iff_some_false (Γ : Set (Formula α)) : ¬ Sat Γ ↔ ∀ v : Val α, ∃ ψ ∈ Γ, ⟦ψ , v⟧ = false := by
      constructor
      · intro h v
        by_contra h'
        have htrue : ∀ ψ ∈ Γ, ⟦ψ , v⟧ = true := by
          intro ψ hψ
          apply Val.bivalence_two v ψ
          intro hfalse
          exact h' ⟨ψ, hψ, hfalse⟩
        have hsat : Sat Γ := ⟨v, htrue⟩
        exact h hsat
      · intro h hsat
        obtain ⟨v, hv⟩ := hsat
        have h' : ∃ ψ ∈ Γ, ⟦ψ , v⟧ = false := by
          apply h v
        obtain ⟨ψ, hψ, hfalse⟩ := h'
        have : ⟦ψ , v⟧ = true := hv ψ hψ
        rw [this] at hfalse
        cases hfalse


@[simp]
lemma sat_monotone {Γ Δ : Set (Formula α)} (h : Sat Δ) (g : Γ ⊆ Δ) : Sat Γ := by
   obtain ⟨v, hv⟩ := h
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
  intro ϕ
  constructor
  · intro h hsat
    obtain ⟨v, hv⟩ := hsat
    have hΓ : ∀ ψ ∈ Γ, ⟦ψ , v⟧ = true :=
      fun ψ hψ => hv ψ (Or.inl hψ)
    have hneg : ⟦¬ϕ , v⟧ = true := hv (¬ϕ) (Or.inr rfl)
    have htrue : ⟦ϕ , v⟧ = true := h v hΓ
    have hfalse : ⟦ϕ , v⟧ = false := (Val.neg_true ϕ v).mp hneg
    rw [htrue] at hfalse
    cases hfalse
  · intro h v hΓ
    by_contra hnotϕ
    have hfalse : ⟦ϕ , v⟧ = false := Val.bivalence_one v ϕ hnotϕ
    have hneg : ⟦¬ϕ , v⟧ = true := (Val.neg_true ϕ v).mpr hfalse
    have hsat : Sat (Γ ∪ {¬ϕ}) := by
      apply Exists.intro v
      intro ψ hψ
      cases hψ with
      | inl hmem => exact hΓ ψ hmem
      | inr hmem =>
        change ψ = Formula.neg ϕ at hmem
        rw [hmem]
        exact hneg
    exact h hsat

@[simp]
lemma non_consequence_iff_sat {Γ : Set (Formula α)} (ϕ : Formula α) :
  (Γ ⊭ ϕ) ↔ Sat (Γ ∪ {¬ϕ}) := by
  constructor
  · intro h
    by_contra hnotSat
    have hcon : Γ ⊨ ϕ :=
      (consequence_iff_not_sat (Γ := Γ) ϕ).mpr hnotSat
    exact h hcon
  · intro hsat hcon
    have hnotSat : ¬ Sat (Γ ∪ {¬ϕ}) :=
      (consequence_iff_not_sat (Γ := Γ) ϕ).mp hcon
    exact hnotSat hsat




@[simp]
lemma refl {Γ : Set (Formula α)} {ϕ : Formula α} (mem : ϕ ∈ Γ) : (Γ ⊨ ϕ) := by
  intro v hΓ
  exact hΓ ϕ mem



@[simp]
lemma monotonicity {Γ Δ : Set (Formula α)} {ϕ : Formula α}
    (h : Γ ⊨ ϕ) (g : Γ ⊆ Δ) : (Δ ⊨ ϕ) := by
  intro v hΔ
  apply h
  intro ψ hψ
  exact hΔ ψ (g hψ)




@[simp]
lemma trans {Γ Δ : Set (Formula α)} {ϕ : Formula α} (h : Γ ⊨ ϕ) : ((Γ ∪ Δ) ⊨ ϕ) := by
  intro v hΔ
  apply h
  intro ψ hψ
  exact hΔ ψ (Or.inl hψ)



@[simp]
lemma conj_intro {Γ Δ : Set (Formula α)} {ϕ ψ : Formula α}
    (h : Γ ⊨ ϕ) (g : Δ ⊨ ψ) : ((Γ ∪ Δ) ⊨ ϕ ∧ ψ) := by
  intro v hUnion
  have hϕ : ⟦ϕ , v⟧ = true := h v (fun θ hθ => hUnion θ (Or.inl hθ))
  have hψ : ⟦ψ , v⟧ = true := g v (fun θ hθ => hUnion θ (Or.inr hθ))
  exact (Val.conj_true ϕ ψ v).mpr ⟨hϕ, hψ⟩


@[simp]
lemma conj_elim_left {Γ : Set (Formula α)} {ϕ ψ : Formula α} (h : Γ ⊨ ϕ ∧ ψ) :
    (Γ ⊨ ϕ) := by
  intro v hΓ
  have hconj : ⟦ϕ ∧ ψ , v⟧ = true := h v hΓ
  exact (Val.conj_true ϕ ψ v).mp hconj |>.1


@[simp]
lemma conj_elim_right {Γ : Set (Formula α)} {ϕ ψ : Formula α} (h : Γ ⊨ ϕ ∧ ψ) :
    (Γ ⊨ ψ) := by
  intro v hΓ
  have hconj : ⟦ϕ ∧ ψ , v⟧ = true := h v hΓ
  exact (Val.conj_true ϕ ψ v).mp hconj |>.2


@[simp]
lemma disj_intro_left {Γ : Set (Formula α)} {ϕ ψ : Formula α}
  (h : Γ ⊨ ϕ) : (Γ ⊨ ϕ ∨ ψ) := by
  intro v hΓ
  have hϕ : ⟦ϕ , v⟧ = true := h v hΓ
  exact (Val.disj_true ϕ ψ v).mpr (Or.inl hϕ)


@[simp]
lemma disj_intro_right {Γ : Set (Formula α)} {ϕ ψ : Formula α}
  (h : Γ ⊨ ψ) : (Γ ⊨ ϕ ∨ ψ) := by
  intro v hΓ
  have hψ : ⟦ψ , v⟧ = true := h v hΓ
  exact (Val.disj_true ϕ ψ v).mpr (Or.inr hψ)


@[simp]
lemma disj_elim {Γ Δ Ξ : Set (Formula α)} {ϕ ψ χ : Formula α}
  (h : Γ ⊨ (ϕ ∨ ψ)) (g : (Δ ∪ {ϕ}) ⊨ χ) (f : (Ξ ∪ {ψ}) ⊨ χ) : ((Γ ∪ Δ ∪ Ξ) ⊨ χ) := by
  intro v hAll
  have hΓ : ∀ θ ∈ Γ, ⟦θ , v⟧ = true := by
    intro θ hθ
    exact hAll θ (Or.inl (Or.inl hθ))
  have hdisj : ⟦ϕ , v⟧ = true ∨ ⟦ψ , v⟧ = true :=
    (Val.disj_true ϕ ψ v).mp (h v hΓ)
  cases hdisj with
  | inl hϕ =>
    apply g v
    intro θ hθ
    cases hθ with
    | inl hθΔ => exact hAll θ (Or.inl (Or.inr hθΔ))
    | inr hθϕ =>
      change θ = ϕ at hθϕ
      rw [hθϕ]
      exact hϕ
  | inr hψ =>
    apply f v
    intro θ hθ
    cases hθ with
    | inl hθΞ => exact hAll θ (Or.inr hθΞ)
    | inr hθψ =>
      change θ = ψ at hθψ
      rw [hθψ]
      exact hψ


@[simp]
lemma imp_intro {Γ : Set (Formula α)} {ϕ ψ : Formula α}
    (h : (Γ ∪ {ϕ}) ⊨ ψ) : (Γ ⊨ ϕ → ψ) := by
  intro v hΓ
  by_cases hϕ : ⟦ϕ , v⟧ = true
  · have hΓϕ : ∀ θ ∈ Γ ∪ {ϕ}, ⟦θ , v⟧ = true := by
      intro θ hθ
      cases hθ with
      | inl hθΓ => exact hΓ θ hθΓ
      | inr hθϕ =>
        change θ = ϕ at hθϕ
        rw [hθϕ]
        exact hϕ
    have hψ : ⟦ψ , v⟧ = true := h v hΓϕ
    exact (Val.imp_true ϕ ψ v).mpr (Or.inr hψ)
  · have hfalse : ⟦ϕ , v⟧ = false := Val.bivalence_one v ϕ hϕ
    exact (Val.imp_true ϕ ψ v).mpr (Or.inl hfalse)


@[simp]
lemma imp_elim {Γ Δ : Set (Formula α)} {ϕ ψ : Formula α} (h : Γ ⊨ ϕ → ψ) (g : Δ ⊨ ϕ) :
    (Γ ∪ Δ ) ⊨ ψ := by
  intro v hUnion
  have hΓ : ∀ θ ∈ Γ, ⟦θ , v⟧ = true := by
    intro θ hθ
    exact hUnion θ (Or.inl hθ)
  have hΔ : ∀ θ ∈ Δ, ⟦θ , v⟧ = true := by
    intro θ hθ
    exact hUnion θ (Or.inr hθ)
  have hImp : ⟦ϕ → ψ , v⟧ = true := h v hΓ
  have hϕ : ⟦ϕ , v⟧ = true := g v hΔ
  have hOr : ⟦ϕ , v⟧ = false ∨ ⟦ψ , v⟧ = true :=
    (Val.imp_true ϕ ψ v).mp hImp
  cases hOr with
  | inl hfalse =>
    rw [hϕ] at hfalse
    cases hfalse
  | inr hψ => exact hψ


end Consequence

def Valid {α : Type u} (ϕ : Formula α) : Prop :=
  ∅ ⊨ ϕ

notation "⊨ " ϕ => Valid ϕ

namespace Valid

variable {α : Type u}

@[simp]
lemma valid_iff {ϕ : Formula α} :
    (⊨ ϕ) ↔  ∀ v : Val α, ⟦ϕ , v⟧ = true := by
  constructor
  · intro h v
    apply h
    intro ψ hψ
    cases hψ
  · intro h v _
    exact h v

@[simp]
lemma bivalid_iff {ϕ : Formula α} :
    (⊨ ϕ) ↔ ¬ Sat {¬ϕ} := by
  constructor
  · intro h hsat
    obtain ⟨v, hv⟩ := hsat
    have hneg : ⟦¬ϕ , v⟧ = true := hv (¬ϕ) rfl
    have htrue : ⟦ϕ , v⟧ = true := (valid_iff.mp h) v
    have hfalse : ⟦ϕ , v⟧ = false := (Val.neg_true ϕ v).mp hneg
    rw [htrue] at hfalse
    cases hfalse
  · intro h
    apply (valid_iff).mpr
    intro v
    by_contra hϕ
    have hfalse : ⟦ϕ , v⟧ = false := Val.bivalence_one v ϕ hϕ
    have hneg : ⟦¬ϕ , v⟧ = true := (Val.neg_true ϕ v).mpr hfalse
    have hsat : Sat {¬ϕ} := by
      apply Exists.intro v
      intro ψ hψ
      change ψ = Formula.neg ϕ at hψ
      rw [hψ]
      exact hneg
    exact h hsat

@[simp]
lemma law_of_excluded_middle (ϕ : Formula α) :
    ⊨ ϕ ∨ ¬ϕ := by
  apply (valid_iff).mpr
  intro v
  apply (Val.disj_true ϕ (Formula.neg ϕ) v).mpr
  cases hϕ : ⟦ϕ , v⟧ with
  | false => exact Or.inr ((Val.neg_true ϕ v).mpr hϕ)
  | true => exact Or.inl rfl

@[simp]
lemma law_of_non_contradiction (ϕ : Formula α) :
    ⊨ ¬(ϕ ∧ ¬ϕ) := by
  apply (valid_iff).mpr
  intro v
  apply (Val.neg_true (Formula.conj ϕ (Formula.neg ϕ)) v).mpr
  apply (Val.conj_false ϕ (Formula.neg ϕ) v).mpr
  cases hϕ : ⟦ϕ , v⟧ with
  | false => exact Or.inl rfl
  | true => exact Or.inr ((Val.neg_false ϕ v).mpr hϕ)

end Valid

def Eqv {α : Type u} (ϕ ψ : Formula α) : Prop :=
  ⊨ (ϕ ↔ ψ)

notation ϕ " ⟚ " ψ => Eqv ϕ ψ

namespace Eqv

variable {α : Type u}

@[simp]
lemma equivalence_to_implication (ϕ ψ : Formula α) :
    (ϕ ⟚ ψ) ↔ (⊨ (ϕ → ψ)) ∧ (⊨ (ψ → ϕ)) := by
  unfold Eqv
  constructor
  · intro h
    constructor
    · apply (Valid.valid_iff).mpr
      intro v
      have hsame : (⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = true) :=
        (Val.iff_true ϕ ψ v).mp ((Valid.valid_iff.mp h) v)
      apply (Val.imp_true ϕ ψ v).mpr
      by_cases hϕ : ⟦ϕ , v⟧ = true
      · exact Or.inr (hsame.mp hϕ)
      · exact Or.inl (Val.bivalence_one v ϕ hϕ)
    · apply (Valid.valid_iff).mpr
      intro v
      have hsame : (⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = true) :=
        (Val.iff_true ϕ ψ v).mp ((Valid.valid_iff.mp h) v)
      apply (Val.imp_true ψ ϕ v).mpr
      by_cases hψ : ⟦ψ , v⟧ = true
      · exact Or.inr (hsame.mpr hψ)
      · exact Or.inl (Val.bivalence_one v ψ hψ)
  · intro h
    apply (Valid.valid_iff).mpr
    intro v
    have hleft : ⟦ϕ → ψ , v⟧ = true := (Valid.valid_iff.mp h.1) v
    have hright : ⟦ψ → ϕ , v⟧ = true := (Valid.valid_iff.mp h.2) v
    have hϕψ : (⟦ϕ , v⟧ = true) → (⟦ψ , v⟧ = true) := by
      intro hϕ
      have hOr := (Val.imp_true ϕ ψ v).mp hleft
      cases hOr with
      | inl hfalse =>
        have hbad : false = true := hfalse.symm.trans hϕ
        cases hbad
      | inr hψ => exact hψ
    have hψϕ : (⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true) := by
      intro hψ
      have hOr := (Val.imp_true ψ ϕ v).mp hright
      cases hOr with
      | inl hfalse =>
        have hbad : false = true := hfalse.symm.trans hψ
        cases hbad
      | inr hϕ => exact hϕ
    exact (Val.iff_true ϕ ψ v).mpr ⟨hϕψ, hψϕ⟩

@[simp]
lemma refl (ϕ : Formula α) : ϕ ⟚ ϕ := by
  unfold Eqv
  apply (Valid.valid_iff).mpr
  intro v
  rw [show ⟦ϕ ↔ ϕ , v⟧ = (⟦ϕ , v⟧ == ⟦ϕ , v⟧) by rfl]
  cases hϕ : ⟦ϕ , v⟧ <;> rfl

@[simp]
lemma symm {ϕ ψ : Formula α} (h : ϕ ⟚ ψ) : ψ ⟚ ϕ := by
  unfold Eqv at h ⊢
  apply (Valid.valid_iff).mpr
  intro v
  have hsame : (⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = true) :=
    (Val.iff_true ϕ ψ v).mp ((Valid.valid_iff.mp h) v)
  exact (Val.iff_true ψ ϕ v).mpr hsame.symm

@[simp]
lemma iff_negation {ϕ ψ : Formula α} (h : ϕ ⟚ ψ) : (¬ϕ) ⟚ (¬ψ) := by
  unfold Eqv at h ⊢
  apply (Valid.valid_iff).mpr
  intro v
  have hiff : ⟦ϕ ↔ ψ , v⟧ = true := (Valid.valid_iff.mp h) v
  rw [show ⟦ϕ ↔ ψ , v⟧ = (⟦ϕ , v⟧ == ⟦ψ , v⟧) by rfl] at hiff
  cases hϕ : ⟦ϕ , v⟧ <;> cases hψ : ⟦ψ , v⟧
  · rw [hϕ, hψ] at hiff
    rw [show ⟦¬ϕ ↔ ¬ψ , v⟧ = (⟦¬ϕ , v⟧ == ⟦¬ψ , v⟧) by rfl]
    rw [show ⟦¬ϕ , v⟧ = !(⟦ϕ , v⟧) by rfl, hϕ]
    rw [show ⟦¬ψ , v⟧ = !(⟦ψ , v⟧) by rfl, hψ]
    rfl
  · rw [hϕ, hψ] at hiff
    cases hiff
  · rw [hϕ, hψ] at hiff
    cases hiff
  · rw [hϕ, hψ] at hiff
    rw [show ⟦¬ϕ ↔ ¬ψ , v⟧ = (⟦¬ϕ , v⟧ == ⟦¬ψ , v⟧) by rfl]
    rw [show ⟦¬ϕ , v⟧ = !(⟦ϕ , v⟧) by rfl, hϕ]
    rw [show ⟦¬ψ , v⟧ = !(⟦ψ , v⟧) by rfl, hψ]
    rfl

@[simp]
lemma iff_conjunction {ϕ₁ ϕ₂ ψ₁ ψ₂ : Formula α}
    (h₁ : ϕ₁ ⟚ ψ₁) (h₂ : ϕ₂ ⟚ ψ₂) :
    (ϕ₁ ∧ ϕ₂) ⟚ (ψ₁ ∧ ψ₂) := by
  unfold Eqv at h₁ h₂ ⊢
  apply (Valid.valid_iff).mpr
  intro v
  have hiff₁ : (⟦ϕ₁ , v⟧ = true) ↔ (⟦ψ₁ , v⟧ = true) := by
    apply (Val.iff_true ϕ₁ ψ₁ v).mp
    exact (Valid.valid_iff.mp h₁) v
  have hiff₂ : (⟦ϕ₂ , v⟧ = true) ↔ (⟦ψ₂ , v⟧ = true) := by
    apply (Val.iff_true ϕ₂ ψ₂ v).mp
    exact (Valid.valid_iff.mp h₂) v
  have hconj :
      (⟦ϕ₁ ∧ ϕ₂ , v⟧ = true) ↔
      (⟦ψ₁ ∧ ψ₂ , v⟧ = true) := by
    constructor
    · intro h
      obtain ⟨hϕ₁, hϕ₂⟩ := (Val.conj_true ϕ₁ ϕ₂ v).mp h
      exact (Val.conj_true ψ₁ ψ₂ v).mpr
        ⟨hiff₁.mp hϕ₁, hiff₂.mp hϕ₂⟩
    · intro h
      obtain ⟨hψ₁, hψ₂⟩ := (Val.conj_true ψ₁ ψ₂ v).mp h
      exact (Val.conj_true ϕ₁ ϕ₂ v).mpr
        ⟨hiff₁.mpr hψ₁, hiff₂.mpr hψ₂⟩
  exact (Val.iff_true (ϕ₁ ∧ ϕ₂) (ψ₁ ∧ ψ₂) v).mpr hconj

end Eqv
