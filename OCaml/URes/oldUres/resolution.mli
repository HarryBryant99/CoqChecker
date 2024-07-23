
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

val list_eq_dec : ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list -> sumbool

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

val opposite : literal -> literal

val lit_eq_dec_bool : literal -> literal -> bool

val is_literal_in_clause_bool : literal -> clause -> bool

val remove : literal -> literal list -> literal list

val remove_literal_from_clause_bool : literal -> clause -> clause

type formula_clause_pair =
| Mk_fcp of formula * clause

type list_of_ures = formula_clause_pair list

val append_to_list_of_ures :
  formula_clause_pair -> list_of_ures -> list_of_ures

val literal_eq_dec : literal -> literal -> sumbool

val fcp_eq_dec : formula_clause_pair -> formula_clause_pair -> bool

val mempu : formula_clause_pair -> list_of_ures -> bool

val check_resolution : clause -> literal -> formula -> list_of_ures -> bool

val compute_resolution :
  clause -> literal -> formula -> list_of_ures -> clause

val is_resolution_complete :
  clause -> literal -> formula -> list_of_ures -> list_of_ures
