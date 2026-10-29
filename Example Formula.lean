import NormalForms.Basic
import NormalForms.NormalFormsFormula

def sample : Formula Nat :=
  .conj (.var 0) (.disj (.var 1) (.neg (.var 2)))


#eval sample.toCNF
#eval sample.toDNF


namespace Formula
#eval toDNF (¬((var 1) ∨ (var 2)))
#eval toNNF (¬((var 1) ∨ (var 2)))
#eval toDNF (toNNF ((var 1) ∨ (var 2)))
#eval toDNF (toNNF ((var 1) ∧ (var 2)))

#eval toDNF (¬((var "p" ∧ var "q") ∨ (var "r" ∨ var "s")))
#eval toNNF (¬((var "p" ∧ var "q") ∨ (var "r" ∨ var "s")))
#eval toCNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q"))

#eval toDNF ((var "p" ∧ var "q") ∨ (var "r" ∧ var "s"))
#eval sortFormula (toDNF ((var "p" ∧ var "q") ∨ (var "r" ∧ var "s")))

#eval toDNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q"))
#eval sortFormula ( toDNF ((var "r" ∧ var "s") ∨ (var "p" ∧ var "q")))

#eval toCNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s"))
#eval toDNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s"))
#eval sortFormula (toCNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))
#eval toDNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s"))



#eval toCNF ((¬ ((var 1) ∧ (var 2))) ∨ (¬ ((var 1) ∨ (¬ (var 2)))))
#eval sortFormula (toCNF ((¬ ((var 1) ∧ (var 2))) ∨ (¬ ((var 1) ∨ (¬ (var 2))))))

end Formula
