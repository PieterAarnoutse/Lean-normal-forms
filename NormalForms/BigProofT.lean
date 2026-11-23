import NormalForms.Basic
import NormalForms.NormalForms_tussentype
import NormalForms.Semantics

universe u

variable {α : Type u}


-- NNF
theorem toNAFormula_sound (φ : Formula α) (v : Val α) :
    Val.eval φ v = Val.eval (NAFormula.toFormula (Formula.toNAFormula φ)) v := by
  induction φ with
  | var a =>
      rfl
  | neg ψ ih =>
      rw [Formula.toNAFormula.eq_2, NAFormula.toFormula.eq_2]
      change Bool.not (Val.eval ψ v) =
        Bool.not (Val.eval (NAFormula.toFormula (Formula.toNAFormula ψ)) v)
      rw [ih]
  | conj ψ χ ihψ ihχ =>
      rw [Formula.toNAFormula.eq_3, NAFormula.toFormula.eq_3]
      change
        (Val.eval ψ v && Val.eval χ v) =
          (Val.eval (NAFormula.toFormula (Formula.toNAFormula ψ)) v &&
            Val.eval (NAFormula.toFormula (Formula.toNAFormula χ)) v)
      rw [ihψ, ihχ]
  | disj ψ χ ihψ ihχ =>
      rw [Formula.toNAFormula.eq_4, NAFormula.toFormula.eq_4]
      change
        (Val.eval ψ v || Val.eval χ v) =
          (Val.eval (NAFormula.toFormula (Formula.toNAFormula ψ)) v ||
            Val.eval (NAFormula.toFormula (Formula.toNAFormula χ)) v)
      rw [ihψ, ihχ]
  | imp ψ χ ihψ ihχ =>
      rw [Formula.toNAFormula.eq_5, NAFormula.toFormula.eq_4,
        NAFormula.toFormula.eq_2]
      change
        (Bool.not (Val.eval ψ v) || Val.eval χ v) =
          (Bool.not (Val.eval (NAFormula.toFormula (Formula.toNAFormula ψ)) v) ||
            Val.eval (NAFormula.toFormula (Formula.toNAFormula χ)) v)
      rw [ihψ, ihχ]
  | iff ψ χ ihψ ihχ =>
      rw [Formula.toNAFormula.eq_6, NAFormula.toFormula.eq_3,
        NAFormula.toFormula.eq_4, NAFormula.toFormula.eq_2]
      change
        (Val.eval ψ v == Val.eval χ v) =
          ((Bool.not (Val.eval (NAFormula.toFormula (Formula.toNAFormula ψ)) v) ||
              Val.eval (NAFormula.toFormula (Formula.toNAFormula χ)) v) &&
            (Bool.not (Val.eval (NAFormula.toFormula (Formula.toNAFormula χ)) v) ||
              Val.eval (NAFormula.toFormula (Formula.toNAFormula ψ)) v))
      rw [ihψ, ihχ]
      cases hψ : Val.eval (NAFormula.toFormula (Formula.toNAFormula ψ)) v <;>
        cases hχ : Val.eval (NAFormula.toFormula (Formula.toNAFormula χ)) v <;>
        decide

theorem naFormula_toNNF_sound_pair (θ : NAFormula α) :
    (∀ v : Val α,
      Val.eval (NAFormula.toFormula θ) v =
        Val.eval (NNF.toFormula (NAFormula.toNNF θ)) v) ∧
    (∀ v : Val α,
      Val.eval (Formula.neg (NAFormula.toFormula θ)) v =
        Val.eval (NNF.toFormula (NAFormula.toNNF (NAFormula.neg θ))) v) := by
  induction θ with
  | var a =>
      constructor
      · intro v
        rw [NAFormula.toFormula.eq_1, NAFormula.toNNF.eq_1,
          NNF.toFormula.eq_1, Lit.toFormula.eq_1]
      · intro v
        rw [NAFormula.toFormula.eq_1, NAFormula.toNNF.eq_2,
          NNF.toFormula.eq_1, Lit.toFormula.eq_2]
  | neg ψ ih =>
      constructor
      · exact ih.2
      · intro v
        rw [NAFormula.toFormula.eq_2, NAFormula.toNNF.eq_3]
        change
          Bool.not (Bool.not (Val.eval (NAFormula.toFormula ψ) v)) =
            Val.eval (NNF.toFormula (NAFormula.toNNF ψ)) v
        rw [ih.1 v]
        cases hψ : Val.eval (NNF.toFormula (NAFormula.toNNF ψ)) v <;>
          decide
  | conj ψ χ ihψ ihχ =>
      constructor
      · intro v
        rw [NAFormula.toFormula.eq_3, NAFormula.toNNF.eq_4,
          NNF.toFormula.eq_2]
        change
          (Val.eval (NAFormula.toFormula ψ) v && Val.eval (NAFormula.toFormula χ) v) =
            (Val.eval (NNF.toFormula (NAFormula.toNNF ψ)) v &&
              Val.eval (NNF.toFormula (NAFormula.toNNF χ)) v)
        rw [ihψ.1 v, ihχ.1 v]
      · intro v
        rw [NAFormula.toFormula.eq_3, NAFormula.toNNF.eq_6,
          NNF.toFormula.eq_3]
        change
          Bool.not (Val.eval (NAFormula.toFormula ψ) v &&
            Val.eval (NAFormula.toFormula χ) v) =
            (Val.eval (NNF.toFormula (NAFormula.toNNF (NAFormula.neg ψ))) v ||
              Val.eval (NNF.toFormula (NAFormula.toNNF (NAFormula.neg χ))) v)
        rw [← ihψ.2 v, ← ihχ.2 v]
        rw [show
          Val.eval (Formula.neg (NAFormula.toFormula ψ)) v =
            Bool.not (Val.eval (NAFormula.toFormula ψ) v) by rfl]
        rw [show
          Val.eval (Formula.neg (NAFormula.toFormula χ)) v =
            Bool.not (Val.eval (NAFormula.toFormula χ) v) by rfl]
        cases hψ : Val.eval (NAFormula.toFormula ψ) v <;>
          cases hχ : Val.eval (NAFormula.toFormula χ) v <;> decide
  | disj ψ χ ihψ ihχ =>
      constructor
      · intro v
        rw [NAFormula.toFormula.eq_4, NAFormula.toNNF.eq_5,
          NNF.toFormula.eq_3]
        change
          (Val.eval (NAFormula.toFormula ψ) v || Val.eval (NAFormula.toFormula χ) v) =
            (Val.eval (NNF.toFormula (NAFormula.toNNF ψ)) v ||
              Val.eval (NNF.toFormula (NAFormula.toNNF χ)) v)
        rw [ihψ.1 v, ihχ.1 v]
      · intro v
        rw [NAFormula.toFormula.eq_4, NAFormula.toNNF.eq_7,
          NNF.toFormula.eq_2]
        change
          Bool.not (Val.eval (NAFormula.toFormula ψ) v ||
            Val.eval (NAFormula.toFormula χ) v) =
            (Val.eval (NNF.toFormula (NAFormula.toNNF (NAFormula.neg ψ))) v &&
              Val.eval (NNF.toFormula (NAFormula.toNNF (NAFormula.neg χ))) v)
        rw [← ihψ.2 v, ← ihχ.2 v]
        rw [show
          Val.eval (Formula.neg (NAFormula.toFormula ψ)) v =
            Bool.not (Val.eval (NAFormula.toFormula ψ) v) by rfl]
        rw [show
          Val.eval (Formula.neg (NAFormula.toFormula χ)) v =
            Bool.not (Val.eval (NAFormula.toFormula χ) v) by rfl]
        cases hψ : Val.eval (NAFormula.toFormula ψ) v <;>
          cases hχ : Val.eval (NAFormula.toFormula χ) v <;> decide

theorem toNNF_sound (φ : Formula α) (v : Val α) :
    Val.eval φ v = Val.eval φ.toNNF v := by
  calc
    Val.eval φ v = Val.eval (NAFormula.toFormula (Formula.toNAFormula φ)) v :=
      toNAFormula_sound φ v
    _ = Val.eval (NNF.toFormula (NAFormula.toNNF (Formula.toNAFormula φ))) v :=
      (naFormula_toNNF_sound_pair (Formula.toNAFormula φ)).1 v
    _ = Val.eval φ.toNNF v := rfl

theorem NNF_eqv : ∀ φ : Formula α, Eqv φ φ.toNNF := by
  intro φ
  unfold Eqv
  apply (Valid.valid_iff).mpr
  intro v
  apply (Val.iff_true φ φ.toNNF v).mpr
  rw [toNNF_sound φ v]


--CNF
theorem distributeClauseCNF_sound (dc : DC α) (c : CNF α) (v : Val α) :
    ⟦CNF.toFormula (CNF.distributeClause dc c), v⟧ =
      ⟦Formula.disj (DC.toFormula dc) (CNF.toFormula c), v⟧ := by
  induction c with
  | disjclause clause =>
      rfl
  | conj left right ihLeft ihRight =>
      simp only [CNF.distributeClause, CNF.toFormula, Val.eval, ihLeft, ihRight]
      cases hdc : Val.eval (DC.toFormula dc) v <;>
        cases hleft : Val.eval (CNF.toFormula left) v <;>
        cases hright : Val.eval (CNF.toFormula right) v <;> decide

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

theorem CNF_sound (φ : Formula α) (v : Val α) :
    ⟦φ, v⟧ = ⟦CNF.toFormula φ.toCNF, v⟧ := by
  rw [toNNF_sound φ v]
  exact NNF_toCNF_sound φ.toNNF v

theorem CNF_eqv : ∀ φ : Formula α, φ ⟚ φ.toCNF := by
  intro φ
  unfold Eqv
  apply (Valid.valid_iff).mpr
  intro v
  apply (Val.iff_true φ (CNF.toFormula φ.toCNF) v).mpr
  rw [CNF_sound φ v]


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

theorem DNF_sound (φ : Formula α) (v : Val α) :
    ⟦φ, v⟧ = ⟦DNF.toFormula φ.toDNF, v⟧ := by
  rw [toNNF_sound φ v]
  exact NNF_toDNF_sound φ.toNNF v

theorem DNF_eqv : ∀ φ : Formula α, φ ⟚ φ.toDNF := by
  intro φ
  unfold Eqv
  apply (Valid.valid_iff).mpr
  intro v
  apply (Val.iff_true φ (DNF.toFormula φ.toDNF) v).mpr
  rw [DNF_sound φ v]
