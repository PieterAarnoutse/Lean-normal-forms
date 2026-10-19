import NormalForms.Basic
import NormalForms.NormalForms

def sample : Formula Nat :=
  .conj (.var 0) (.disj (.var 1) (.neg (.var 2)))


#eval sample.toNNF.toCNF
#eval sample.toNNF.toDNF


namespace Formula
#eval NNF.toDNF (toNNF ((var 1) ∨ (var 2)))
#eval NNF.toDNF (toNNF ((var 1) ∧ (var 2)))

#eval NNF.toCNF (toNNF ((var "p" ∧ var "q") ∨ (var "r" ∧ var "s")))
#eval NNF.toCNF (toNNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q")))

#eval NNF.toDNF (toNNF ((var "p" ∧ var "q") ∨ (var "r" ∧ var "s")))
#eval NNF.toDNF (toNNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q")))

#eval NNF.toCNF (toNNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))
#eval NNF.toDNF (toNNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))

#eval NNF.toCNF (Formula.toNNF ((¬ ((var 1) ∧ (var 2))) ∨ (¬ ((var 1) ∨ (¬ (var 2))))))

end Formula
