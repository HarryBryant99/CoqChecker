
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type sumbool =
| Left
| Right

val leb : nat -> nat -> bool

val ltb : nat -> nat -> bool

val bool_dec : bool -> bool -> sumbool

val eqb : bool -> bool -> bool

val nth : nat -> 'a1 list -> 'a1 -> 'a1

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_dec : ascii -> ascii -> sumbool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val string_dec : string -> string -> sumbool

val eqb1 : string -> string -> bool

type literal =
| Pos of string
| Neg of string

type clause = literal list

type proofStep =
| Ass of nat
| Res of nat * nat * clause

type preProof = proofStep list

type assumption = clause list

type conclusion = clause list

val length : 'a1 list -> nat

val findAssumption : assumption -> nat -> clause

val findConclusion : nat -> conclusion -> clause

val lit_eq_dec_bool : literal -> literal -> bool

val remove2 : literal -> literal list -> literal list

val remove_literal_from_clause_bool : literal -> clause -> clause

val opposite : literal -> literal

val clause_head : clause -> literal -> literal

val toResConclusion : clause -> clause -> clause

val conclusions : assumption -> preProof -> conclusion

val ltb0 : nat -> nat -> bool

val is_unit_clause : clause -> bool

val is_literal_in_clause_bool : literal -> clause -> bool

val literal_eqb : literal -> literal -> bool

val clause_eqb : clause -> clause -> bool

val isRes : clause -> clause -> clause -> bool

val isCorrectLastStep : assumption -> conclusion -> proofStep -> bool

val checkAll : assumption -> preProof -> conclusion -> bool

val isCorrect : assumption -> preProof -> bool
