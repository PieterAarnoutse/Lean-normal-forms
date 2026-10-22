import NormalForms.Basic
import NormalForms.NormalFormsNoNNF

def sample : Formula Nat :=
  .conj (.var 0) (.disj (.var 1) (.neg (.var 2)))


#eval sample.toNNF.toCNF
#eval sample.toNNF.toDNF


namespace Formula
#eval toDNF ((var 1) ∨ (var 2))
#eval toNNF ((var 1) ∨ (var 2))
#eval toDNF (toNNF ((var 1) ∨ (var 2)))
#eval toDNF (toNNF ((var 1) ∧ (var 2)))

#eval toCNF (toNNF ((var "p" ∧ var "q") ∨ (var "r" ∧ var "s")))
#eval toCNF (toNNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q")))

#eval toDNF (toNNF ((var "p" ∧ var "q") ∨ (var "r" ∧ var "s")))
#eval toDNF (toNNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q")))

#eval toCNF (toNNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))
#eval toDNF (toNNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))



#eval toCNF (Formula.toNNF ((¬ ((var 1) ∧ (var 2))) ∨ (¬ ((var 1) ∨ (¬ (var 2))))))

end Formula
