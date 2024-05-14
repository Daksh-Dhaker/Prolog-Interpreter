type term = Variable of string | Constant of string |Int of int| Function of string * term list | Set of term list | Pipe of term*term
type atomic_formula = Predicate of string * term list
type body = atomic_formula list
type clause = Fact of atomic_formula | Rule of atomic_formula * body
type program = clause list