
type bool =
| True
| False

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

type literal =
| Pos of string
| Neg of string

(** val opposite : literal -> literal **)

let opposite = function
| Pos s -> Neg s
| Neg s -> Pos s
