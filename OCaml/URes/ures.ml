
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type sumbool =
| Left
| Right

(** val leb : nat -> nat -> bool **)

let rec leb n m =
  match n with
  | O -> True
  | S n' -> (match m with
             | O -> False
             | S m' -> leb n' m')

(** val ltb : nat -> nat -> bool **)

let ltb n m =
  leb (S n) m

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default
            | Cons (_, t) -> nth m t default)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_dec : ascii -> ascii -> sumbool **)

let ascii_dec a b =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match bool_dec b0 b8 with
   | Left ->
     (match bool_dec b1 b9 with
      | Left ->
        (match bool_dec b2 b10 with
         | Left ->
           (match bool_dec b3 b11 with
            | Left ->
              (match bool_dec b4 b12 with
               | Left ->
                 (match bool_dec b5 b13 with
                  | Left ->
                    (match bool_dec b6 b14 with
                     | Left -> bool_dec b7 b15
                     | Right -> Right)
                  | Right -> Right)
               | Right -> Right)
            | Right -> Right)
         | Right -> Right)
      | Right -> Right)
   | Right -> Right)

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val string_dec : string -> string -> sumbool **)

let rec string_dec s x =
  match s with
  | EmptyString -> (match x with
                    | EmptyString -> Left
                    | String (_, _) -> Right)
  | String (a, s0) ->
    (match x with
     | EmptyString -> Right
     | String (a0, s1) ->
       (match ascii_dec a a0 with
        | Left -> string_dec s0 s1
        | Right -> Right))

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

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

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val findAssumption : assumption -> preProof -> nat -> clause **)

let findAssumption ass _ i =
  nth i ass Nil

(** val findConclusion : nat -> conclusion -> clause **)

let findConclusion i r =
  nth i r Nil

(** val lit_eq_dec_bool : literal -> literal -> bool **)

let lit_eq_dec_bool a b =
  match a with
  | Pos s1 ->
    (match b with
     | Pos s2 -> (match string_dec s1 s2 with
                  | Left -> True
                  | Right -> False)
     | Neg _ -> False)
  | Neg s1 ->
    (match b with
     | Pos _ -> False
     | Neg s2 -> (match string_dec s1 s2 with
                  | Left -> True
                  | Right -> False))

(** val remove : literal -> literal list -> literal list **)

let rec remove x = function
| Nil -> Nil
| Cons (y, tl) ->
  (match lit_eq_dec_bool x y with
   | True -> remove x tl
   | False -> Cons (y, (remove x tl)))

(** val remove_literal_from_clause_bool : literal -> clause -> clause **)

let remove_literal_from_clause_bool =
  remove

(** val opposite : literal -> literal **)

let opposite = function
| Pos s -> Neg s
| Neg s -> Pos s

(** val clause_head : clause -> literal -> literal **)

let clause_head c default =
  match c with
  | Nil -> default
  | Cons (l, _) -> l

(** val toResConclusion : clause -> clause -> clause **)

let toResConclusion c1 c2 =
  remove_literal_from_clause_bool
    (opposite (clause_head c2 (Pos EmptyString))) c1

(** val get_k : proofStep -> clause **)

let get_k = function
| Ass _ -> Nil
| Res (_, _, k) -> k

(** val add_clause : conclusion -> clause -> conclusion **)

let add_clause r c =
  app r (Cons (c, Nil))

(** val conclusions : assumption -> conclusion -> preProof -> conclusion **)

let rec conclusions ass r p = match p with
| Nil -> r
| Cons (step, tl) ->
  (match step with
   | Ass i ->
     let r' = add_clause r (findAssumption ass p i) in conclusions ass r' tl
   | Res (_, _, _) ->
     let r' = add_clause r (get_k step) in conclusions ass r' tl)

(** val ltb0 : nat -> nat -> bool **)

let ltb0 =
  ltb

(** val is_unit_clause : clause -> bool **)

let is_unit_clause = function
| Nil -> False
| Cons (_, l) -> (match l with
                  | Nil -> True
                  | Cons (_, _) -> False)

(** val is_literal_in_clause_bool : literal -> clause -> bool **)

let rec is_literal_in_clause_bool l = function
| Nil -> False
| Cons (hd, tl) ->
  (match lit_eq_dec_bool l hd with
   | True -> True
   | False -> is_literal_in_clause_bool l tl)

(** val literal_eqb : literal -> literal -> bool **)

let literal_eqb l1 l2 =
  match l1 with
  | Pos s1 -> (match l2 with
               | Pos s2 -> eqb1 s1 s2
               | Neg _ -> False)
  | Neg s1 -> (match l2 with
               | Pos _ -> False
               | Neg s2 -> eqb1 s1 s2)

(** val clause_eqb : clause -> clause -> bool **)

let rec clause_eqb c1 c2 =
  match c1 with
  | Nil -> (match c2 with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (l1, c1') ->
    (match c2 with
     | Nil -> False
     | Cons (l2, c2') ->
       (match literal_eqb l1 l2 with
        | True -> clause_eqb c1' c2'
        | False -> False))

(** val isRes : clause -> clause -> clause -> bool **)

let isRes c1 c2 k =
  match match is_unit_clause c2 with
        | True ->
          is_literal_in_clause_bool
            (opposite (clause_head c2 (Pos EmptyString))) c1
        | False -> False with
  | True -> clause_eqb (toResConclusion c1 c2) k
  | False -> False

(** val isCorrectLastStep :
    assumption -> conclusion -> proofStep -> preProof -> bool **)

let isCorrectLastStep ass conclusionpl p _ =
  match p with
  | Ass n -> ltb0 n (length ass)
  | Res (n, m, k) ->
    let lengthConcll = length conclusionpl in
    (match ltb0 n lengthConcll with
     | True ->
       (match ltb0 m lengthConcll with
        | True ->
          isRes (findConclusion n conclusionpl)
            (findConclusion m conclusionpl) k
        | False -> False)
     | False -> False)

(** val checkAll : assumption -> conclusion -> preProof -> bool **)

let rec checkAll ass conclusionpl pl = match pl with
| Nil -> True
| Cons (p, l) ->
  (match isCorrectLastStep ass conclusionpl p pl with
   | True -> checkAll ass conclusionpl l
   | False -> False)

(** val isCorrect : assumption -> preProof -> bool **)

let isCorrect ass pl =
  let conclusionpl = conclusions ass Nil pl in checkAll ass conclusionpl pl
