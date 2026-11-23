import NormalForms.Basic
import NormalForms.NormalForms_Mutual
import NormalForms.Semantics

universe u

variable {α : Type u}


--NNF
private theorem toNNF_sound_pair (φ : Formula α) :
    (∀ v : Val α, ⟦φ, v⟧ = ⟦φ.toNNF, v⟧) ∧
    (∀ v : Val α,
      ⟦Formula.neg φ, v⟧ = ⟦Formula.toNNFNeg φ, v⟧) := by
  induction φ with
  | var a =>
    constructor <;> intro v <;> rfl
  | neg ψ ih =>
    constructor
    · exact ih.2
    · intro v
      rw [Formula.toNNFNeg_neg]
      change Bool.not (Bool.not ⟦ψ, v⟧) = ⟦ψ.toNNF, v⟧
      rw [← ih.1 v]
      cases hψ : ⟦ψ, v⟧ <;> rfl
  | conj ψ χ ihψ ihχ =>
    constructor
    · intro v
      change (⟦ψ, v⟧ && ⟦χ, v⟧) =
        (⟦ψ.toNNF, v⟧ && ⟦χ.toNNF, v⟧)
      rw [ihψ.1 v, ihχ.1 v]
    · intro v
      rw [Formula.toNNFNeg_conj, NNF.toFormula]
      change Bool.not (⟦ψ, v⟧ && ⟦χ, v⟧) =
        (⟦Formula.toNNFNeg ψ, v⟧ || ⟦Formula.toNNFNeg χ, v⟧)
      rw [← ihψ.2 v, ← ihχ.2 v]
      rw [show ⟦Formula.neg ψ, v⟧ = Bool.not ⟦ψ, v⟧ by rfl]
      rw [show ⟦Formula.neg χ, v⟧ = Bool.not ⟦χ, v⟧ by rfl]
      cases hψ : ⟦ψ, v⟧ <;> cases hχ : ⟦χ, v⟧ <;> rfl
  | disj ψ χ ihψ ihχ =>
    constructor
    · intro v
      change (⟦ψ, v⟧ || ⟦χ, v⟧) =
        (⟦ψ.toNNF, v⟧ || ⟦χ.toNNF, v⟧)
      rw [ihψ.1 v, ihχ.1 v]
    · intro v
      rw [Formula.toNNFNeg_disj, NNF.toFormula]
      change Bool.not (⟦ψ, v⟧ || ⟦χ, v⟧) =
        (⟦Formula.toNNFNeg ψ, v⟧ && ⟦Formula.toNNFNeg χ, v⟧)
      rw [← ihψ.2 v, ← ihχ.2 v]
      rw [show ⟦Formula.neg ψ, v⟧ = Bool.not ⟦ψ, v⟧ by rfl]
      rw [show ⟦Formula.neg χ, v⟧ = Bool.not ⟦χ, v⟧ by rfl]
      cases hψ : ⟦ψ, v⟧ <;> cases hχ : ⟦χ, v⟧ <;> rfl
  | imp ψ χ ihψ ihχ =>
    constructor
    · intro v
      change (!⟦ψ, v⟧ || ⟦χ, v⟧) =
        (⟦Formula.toNNFNeg ψ, v⟧ || ⟦χ.toNNF, v⟧)
      rw [← ihψ.2 v, ← ihχ.1 v]
      rfl
    · intro v
      rw [Formula.toNNFNeg_imp, NNF.toFormula]
      change Bool.not (Bool.not ⟦ψ, v⟧ || ⟦χ, v⟧) =
        (⟦Formula.toNNF ψ, v⟧ && ⟦Formula.toNNFNeg χ, v⟧)
      rw [← ihψ.1 v, ← ihχ.2 v]
      rw [show ⟦Formula.neg χ, v⟧ = Bool.not ⟦χ, v⟧ by rfl]
      cases hψ : ⟦ψ, v⟧ <;> cases hχ : ⟦χ, v⟧ <;> rfl
  | iff ψ χ ihψ ihχ =>
    constructor
    · intro v
      change (⟦ψ, v⟧ == ⟦χ, v⟧) =
        ((⟦Formula.toNNFNeg ψ, v⟧ || ⟦χ.toNNF, v⟧) &&
          (⟦Formula.toNNFNeg χ, v⟧ || ⟦ψ.toNNF, v⟧))
      rw [← ihψ.2 v, ← ihχ.1 v, ← ihχ.2 v, ← ihψ.1 v]
      rw [show ⟦Formula.neg ψ, v⟧ = Bool.not ⟦ψ, v⟧ by rfl]
      rw [show ⟦Formula.neg χ, v⟧ = Bool.not ⟦χ, v⟧ by rfl]
      cases hψ : ⟦ψ, v⟧ <;> cases hχ : ⟦χ, v⟧ <;> rfl
    · intro v
      rw [Formula.toNNFNeg_iff, NNF.toFormula]
      change Bool.not (⟦ψ, v⟧ == ⟦χ, v⟧) =
        ((⟦Formula.toNNF ψ, v⟧ && ⟦Formula.toNNFNeg χ, v⟧) ||
          (⟦Formula.toNNF χ, v⟧ && ⟦Formula.toNNFNeg ψ, v⟧))
      rw [← ihψ.1 v, ← ihχ.2 v, ← ihχ.1 v, ← ihψ.2 v]
      rw [show ⟦Formula.neg ψ, v⟧ = Bool.not ⟦ψ, v⟧ by rfl]
      rw [show ⟦Formula.neg χ, v⟧ = Bool.not ⟦χ, v⟧ by rfl]
      cases hψ : ⟦ψ, v⟧ <;> cases hχ : ⟦χ, v⟧ <;> rfl

theorem toNNF_sound (φ : Formula α) (v : Val α) :
    ⟦φ, v⟧ = ⟦φ.toNNF, v⟧ :=
  (toNNF_sound_pair φ).1 v

theorem toNNFNeg_sound (φ : Formula α) (v : Val α) :
    ⟦Formula.neg φ, v⟧ = ⟦Formula.toNNFNeg φ, v⟧ :=
  (toNNF_sound_pair φ).2 v

theorem NNF_eqv (φ : Formula α) : φ ⟚ φ.toNNF := by
  unfold Eqv
  apply (Valid.valid_iff).mpr
  intro v
  have hEval := toNNF_sound φ v
  apply (Val.iff_true φ φ.toNNF v).mpr
  rw [hEval]


--CNF
theorem distributeClauseCNF_sound (dc : DC α) (c : CNF α) (v : Val α) :
    ⟦CNF.toFormula (CNF.distributeClause dc c), v⟧ =
      ⟦Formula.disj (DC.toFormula dc) (CNF.toFormula c), v⟧ := by
  induction c with
  | disjclause clause =>
      rfl
  | conj left right ihLeft ihRight =>
      unfold CNF.distributeClause
      change
        ⟦Formula.conj
          (CNF.toFormula (CNF.distributeClause dc left))
          (CNF.toFormula (CNF.distributeClause dc right)), v⟧ =
        ⟦Formula.disj (DC.toFormula dc)
          (Formula.conj (CNF.toFormula left) (CNF.toFormula right)), v⟧
      rw [show
        ⟦Formula.conj
          (CNF.toFormula (CNF.distributeClause dc left))
          (CNF.toFormula (CNF.distributeClause dc right)), v⟧ =
            (⟦CNF.toFormula (CNF.distributeClause dc left), v⟧ &&
              ⟦CNF.toFormula (CNF.distributeClause dc right), v⟧) by rfl]
      rw [show
        ⟦Formula.disj (DC.toFormula dc)
          (Formula.conj (CNF.toFormula left) (CNF.toFormula right)), v⟧ =
            (⟦DC.toFormula dc, v⟧ ||
              (⟦CNF.toFormula left, v⟧ && ⟦CNF.toFormula right, v⟧)) by rfl]
      rw [ihLeft, ihRight]
      rw [show
        ⟦Formula.disj (DC.toFormula dc) (CNF.toFormula left), v⟧ =
          (⟦DC.toFormula dc, v⟧ || ⟦CNF.toFormula left, v⟧) by rfl]
      rw [show
        ⟦Formula.disj (DC.toFormula dc) (CNF.toFormula right), v⟧ =
          (⟦DC.toFormula dc, v⟧ || ⟦CNF.toFormula right, v⟧) by rfl]
      cases hdc : ⟦DC.toFormula dc, v⟧ <;>
        cases hleft : ⟦CNF.toFormula left, v⟧ <;>
        cases hright : ⟦CNF.toFormula right, v⟧ <;> decide

theorem distributeDisjCNF_sound (left right : CNF α) (v : Val α) :
    ⟦CNF.toFormula (CNF.distributeDisj left right), v⟧ =
      ⟦Formula.disj (CNF.toFormula left) (CNF.toFormula right), v⟧ := by
  induction left with
  | disjclause dc =>
      exact distributeClauseCNF_sound dc right v
  | conj p q ihP ihQ =>
      change
        (⟦CNF.toFormula (CNF.distributeDisj p right), v⟧ &&
          ⟦CNF.toFormula (CNF.distributeDisj q right), v⟧) =
        ((⟦CNF.toFormula p, v⟧ && ⟦CNF.toFormula q, v⟧) ||
          ⟦CNF.toFormula right, v⟧)
      rw [ihP, ihQ]
      change
        ((⟦CNF.toFormula p, v⟧ || ⟦CNF.toFormula right, v⟧) &&
          (⟦CNF.toFormula q, v⟧ || ⟦CNF.toFormula right, v⟧)) =
        ((⟦CNF.toFormula p, v⟧ && ⟦CNF.toFormula q, v⟧) ||
          ⟦CNF.toFormula right, v⟧)
      cases hp : ⟦CNF.toFormula p, v⟧ <;>
        cases hq : ⟦CNF.toFormula q, v⟧ <;>
        cases hr : ⟦CNF.toFormula right, v⟧ <;>
        rfl

theorem NNF_toCNF_sound (n : NNF α) (v : Val α) :
    ⟦NNF.toFormula n, v⟧ =
      ⟦CNF.toFormula (NNF.toCNF n), v⟧ := by
  induction n with
  | lit literal =>
      rfl
  | conj left right ihLeft ihRight =>
      change
        (⟦NNF.toFormula left, v⟧ && ⟦NNF.toFormula right, v⟧) =
        (⟦CNF.toFormula (NNF.toCNF left), v⟧ &&
          ⟦CNF.toFormula (NNF.toCNF right), v⟧)
      rw [ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      change
        (⟦NNF.toFormula left, v⟧ || ⟦NNF.toFormula right, v⟧) =
        ⟦CNF.toFormula
          (CNF.distributeDisj (NNF.toCNF left) (NNF.toCNF right)), v⟧
      rw [distributeDisjCNF_sound]
      rw [show
        ⟦Formula.disj (CNF.toFormula (NNF.toCNF left))
          (CNF.toFormula (NNF.toCNF right)), v⟧ =
            (⟦CNF.toFormula (NNF.toCNF left), v⟧ ||
              ⟦CNF.toFormula (NNF.toCNF right), v⟧) by rfl]
      rw [ihLeft, ihRight]

theorem CNF_eqv (φ : Formula α) : φ ⟚ φ.toCNF := by
  unfold Eqv
  apply (Valid.valid_iff).mpr
  intro v
  have hEval : ⟦φ, v⟧ = ⟦CNF.toFormula φ.toCNF, v⟧ := by
    rw [toNNF_sound φ v]
    exact NNF_toCNF_sound φ.toNNF v
  apply (Val.iff_true φ (CNF.toFormula φ.toCNF) v).mpr
  rw [hEval]


-- DNF
theorem distributeClauseDNF_sound (cc : CC α) (d : DNF α) (v : Val α) :
    ⟦DNF.toFormula (DNF.distributeClause cc d), v⟧ =
      ⟦Formula.conj (CC.toFormula cc) (DNF.toFormula d), v⟧ := by
  induction d with
  | conjclause clause =>
      rfl
  | disj left right ihLeft ihRight =>
      change
        (⟦DNF.toFormula (DNF.distributeClause cc left), v⟧ ||
          ⟦DNF.toFormula (DNF.distributeClause cc right), v⟧) =
        (⟦CC.toFormula cc, v⟧ &&
          (⟦DNF.toFormula left, v⟧ || ⟦DNF.toFormula right, v⟧))
      rw [ihLeft, ihRight]
      change
        ((⟦CC.toFormula cc, v⟧ && ⟦DNF.toFormula left, v⟧) ||
          (⟦CC.toFormula cc, v⟧ && ⟦DNF.toFormula right, v⟧)) =
        (⟦CC.toFormula cc, v⟧ &&
          (⟦DNF.toFormula left, v⟧ || ⟦DNF.toFormula right, v⟧))
      cases hcc : ⟦CC.toFormula cc, v⟧ <;>
        cases hleft : ⟦DNF.toFormula left, v⟧ <;>
        cases hright : ⟦DNF.toFormula right, v⟧ <;>
        rfl

theorem distributeConjDNF_sound (left right : DNF α) (v : Val α) :
    ⟦DNF.toFormula (DNF.distributeConj left right), v⟧ =
      ⟦Formula.conj (DNF.toFormula left) (DNF.toFormula right), v⟧ := by
  induction left with
  | conjclause cc =>
      exact distributeClauseDNF_sound cc right v
  | disj p q ihP ihQ =>
      change
        (⟦DNF.toFormula (DNF.distributeConj p right), v⟧ ||
          ⟦DNF.toFormula (DNF.distributeConj q right), v⟧) =
        ((⟦DNF.toFormula p, v⟧ || ⟦DNF.toFormula q, v⟧) &&
          ⟦DNF.toFormula right, v⟧)
      rw [ihP, ihQ]
      change
        ((⟦DNF.toFormula p, v⟧ && ⟦DNF.toFormula right, v⟧) ||
          (⟦DNF.toFormula q, v⟧ && ⟦DNF.toFormula right, v⟧)) =
        ((⟦DNF.toFormula p, v⟧ || ⟦DNF.toFormula q, v⟧) &&
          ⟦DNF.toFormula right, v⟧)
      cases hp : ⟦DNF.toFormula p, v⟧ <;>
        cases hq : ⟦DNF.toFormula q, v⟧ <;>
        cases hr : ⟦DNF.toFormula right, v⟧ <;>
        rfl

theorem NNF_toDNF_sound (n : NNF α) (v : Val α) :
    ⟦NNF.toFormula n, v⟧ =
      ⟦DNF.toFormula (NNF.toDNF n), v⟧ := by
  induction n with
  | lit literal =>
      rfl
  | conj left right ihLeft ihRight =>
      change
        (⟦NNF.toFormula left, v⟧ && ⟦NNF.toFormula right, v⟧) =
        ⟦DNF.toFormula
          (DNF.distributeConj (NNF.toDNF left) (NNF.toDNF right)), v⟧
      rw [distributeConjDNF_sound]
      rw [show
        ⟦Formula.conj (DNF.toFormula (NNF.toDNF left))
          (DNF.toFormula (NNF.toDNF right)), v⟧ =
            (⟦DNF.toFormula (NNF.toDNF left), v⟧ &&
              ⟦DNF.toFormula (NNF.toDNF right), v⟧) by rfl]
      rw [ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      change
        (⟦NNF.toFormula left, v⟧ || ⟦NNF.toFormula right, v⟧) =
        (⟦DNF.toFormula (NNF.toDNF left), v⟧ ||
          ⟦DNF.toFormula (NNF.toDNF right), v⟧)
      rw [ihLeft, ihRight]

theorem DNF_eqv (φ : Formula α) : φ ⟚ φ.toDNF := by
  unfold Eqv
  apply (Valid.valid_iff).mpr
  intro v
  have hEval : ⟦φ, v⟧ = ⟦DNF.toFormula φ.toDNF, v⟧ := by
    rw [toNNF_sound φ v]
    exact NNF_toDNF_sound φ.toNNF v
  apply (Val.iff_true φ (DNF.toFormula φ.toDNF) v).mpr
  rw [hEval]
