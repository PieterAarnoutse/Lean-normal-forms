import NormalForms.Basic
import NormalForms.NormalFormsNNF
set_option linter.style.longLine false

def sample : Formula Nat :=
  .conj (.var 0) (.disj (.var 1) (.neg (.var 2)))


#eval sample.toNNF.toCNF
#eval sample.toNNF.toDNF


namespace Formula
#eval toDNF ((var 1) ∨ (var 2))
#eval toDNF ((var 1) ∧ (var 2))

#eval NNF.toCNF (toNNF ((var "p" ∧  "q") ∨ ( "r" ∧  "s")))
#eval NNF.toCNF (toNNF (((var "r" ∧ var "s") ∨ (var "p" ∧ var "q" ))))

#eval NNF.toDNF (toNNF ((var "p" ∧ var "q") ∨ (var "r" ∧ var "s")))
#eval NNF.toDNF (toNNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q")))

#eval NNF.toCNF (toNNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))
#eval NNF.toDNF (toNNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))


#eval ( DNFtoFormula ( toDNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s"))))
/- Haakjes nog wel een ding, sommige zijn overbodig -/


#eval ( CNFtoFormula ( toCNF ((¬ ((var 1) ∧ (var 2))) ∨ (¬ ((var 1) ∨ (¬ (var 2)))))))


end Formula
