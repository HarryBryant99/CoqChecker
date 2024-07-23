
type bool =
| True
| False

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

type literal =
| Pos of string
| Neg of string

(** val opposite : literal -> literal **)

let opposite = function
| Pos s -> Neg s
| Neg s -> Pos s

(** val transform_literal : string -> literal -> literal **)

let transform_literal prefix = function
| Pos s -> Pos (append prefix s)
| Neg s -> Neg (append prefix s)
