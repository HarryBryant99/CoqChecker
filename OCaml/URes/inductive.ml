
type bool =
| True
| False

type 'a list =
| Nil
| Cons of 'a * 'a list

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

type literal =
| Pos of string
| Neg of string

type clause = literal list

type formula = clause list

type unitres =
| Subsumption of clause * clause * formula
| Resolution of clause * literal * formula * unitres * unitres
