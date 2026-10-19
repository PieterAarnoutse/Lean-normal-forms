import NormalForms.NormalFormsList

def sample : Formula Nat :=
  .conj (.var 0) (.disj (.var 1) (.neg (.var 2)))

#eval sample.nnf
#eval sample.dnf.clauses  -- 2
#eval sample.cnf.clauses  -- 2

def empty_sample : Formula Nat :=
  .bot



example (a : Nat) :
    Formula.nnf (.neg (.neg (.var a))) = Formula.nnf (.var a) := rfl
