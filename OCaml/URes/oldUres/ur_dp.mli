
type bool =
| True
| False

type 'a list =
| Nil
| Cons of 'a * 'a list

type sumbool =
| Left
| Right

val bool_dec : bool -> bool -> sumbool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_dec : ascii -> ascii -> sumbool

type string =
| EmptyString
| String of ascii * string

val string_dec : string -> string -> sumbool

type literal =
| Pos of string
| Neg of string

type clause = literal list

type formula = clause list

val literal_eq_dec : literal -> literal -> sumbool

val literal_eq : literal -> literal -> bool

val clause_eq_dec : clause -> clause -> bool

val memcf : clause -> formula -> bool

val inb : literal -> clause -> bool

val subset : clause -> clause -> bool

type formula_clause_pair =
| Mk_fcp of formula * clause

type list_of_ures = formula_clause_pair list

val check_subsumption : clause -> clause -> formula -> bool

val append_to_list_of_ures :
  formula_clause_pair -> list_of_ures -> list_of_ures

val compute_subsumption :
  clause -> clause -> formula -> list_of_ures -> list_of_ures
