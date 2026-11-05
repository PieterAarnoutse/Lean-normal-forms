import NormalForms.Basic
import NormalForms.NormalForms
set_option linter.style.longLine false

def sample : Formula Nat :=
  .conj (.var 0) (.disj (.var 1) (.neg (.var 2)))


#eval sample.toCNF
#eval sample.toDNF


namespace Formula
#eval toDNF ((var 1) ∨ (var 2))
#eval toDNF ((var 1) ∧ (var 2))

#eval toCNF ((var "p" ∧  var "q" ∧ var "r") ∨ ( var "r" ∧  var "s"))
#eval toCNF (((var "r" ∧ var "s") ∨ (var "p" ∧ var "q" ∧ var "r")))

#eval toDNF ((var "p" ∧  var "q" ∧ neg (var "r")) ∨ ( var "r" ∧  var "s"))
#eval toDNF (((var "r" ∧ var "s") ∨ (var "p" ∧ var "q" ∧ var "r")))

#eval toNNF ((var "p" ∨ var "q" ∨ var "s") ∧ (var "r" ∨ var "s"))
#eval NNF.toCNF (toNNF (neg ((var "p" ∨ var "q" ∨ var "s") ∧ (var "r" ∨ var "s"))))
#eval NNF.toDNF (toNNF ((var "p" ∨ var "q") ∧ (var "r" ∨ var "s")))


end Formula
