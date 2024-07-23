
type bool =
| True
| False

type 'a list =
| Nil
| Cons of 'a * 'a list

type sumbool =
| Left
| Right

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

(** val list_eq_dec :
    ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list -> sumbool **)

let rec list_eq_dec eq_dec l l' =
  match l with
  | Nil -> (match l' with
            | Nil -> Left
            | Cons (_, _) -> Right)
  | Cons (y, l0) ->
    (match l' with
     | Nil -> Right
     | Cons (a, l1) ->
       (match eq_dec y a with
        | Left -> list_eq_dec eq_dec l0 l1
        | Right -> Right))

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

type literal =
| Pos of string
| Neg of string

type clause = literal list

type formula = clause list

(** val opposite : literal -> literal **)

let opposite = function
| Pos s -> Neg s
| Neg s -> Pos s

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

(** val is_literal_in_clause_bool : literal -> clause -> bool **)

let rec is_literal_in_clause_bool l = function
| Nil -> False
| Cons (hd, tl) ->
  (match lit_eq_dec_bool l hd with
   | True -> True
   | False -> is_literal_in_clause_bool l tl)

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

type formula_clause_pair =
| Mk_fcp of formula * clause

type list_of_ures = formula_clause_pair list

(** val append_to_list_of_ures :
    formula_clause_pair -> list_of_ures -> list_of_ures **)

let append_to_list_of_ures n s =
  Cons (n, s)

(** val literal_eq_dec : literal -> literal -> sumbool **)

let literal_eq_dec l1 l2 =
  match l1 with
  | Pos s -> (match l2 with
              | Pos s0 -> string_dec s s0
              | Neg _ -> Right)
  | Neg s -> (match l2 with
              | Pos _ -> Right
              | Neg s0 -> string_dec s s0)

(** val fcp_eq_dec : formula_clause_pair -> formula_clause_pair -> bool **)

let fcp_eq_dec a b =
  let Mk_fcp (f1, c1) = a in
  let Mk_fcp (f2, c2) = b in
  (match list_eq_dec (list_eq_dec literal_eq_dec) f1 f2 with
   | Left ->
     (match list_eq_dec literal_eq_dec c1 c2 with
      | Left -> True
      | Right -> False)
   | Right -> False)

(** val mempu : formula_clause_pair -> list_of_ures -> bool **)

let rec mempu a = function
| Nil -> False
| Cons (b, m) -> (match fcp_eq_dec a b with
                  | True -> True
                  | False -> mempu a m)

(** val check_resolution :
    clause -> literal -> formula -> list_of_ures -> bool **)

let check_resolution c l f s =
  match mempu (Mk_fcp (f, c)) s with
  | True ->
    (match is_literal_in_clause_bool l c with
     | True -> mempu (Mk_fcp (f, (Cons ((opposite l), Nil)))) s
     | False -> False)
  | False -> False

(** val compute_resolution :
    clause -> literal -> formula -> list_of_ures -> clause **)

let compute_resolution c l f s =
  match check_resolution c l f s with
  | True -> remove_literal_from_clause_bool l c
  | False -> c

(** val is_resolution_complete :
    clause -> literal -> formula -> list_of_ures -> list_of_ures **)

let is_resolution_complete c l f s =
  let result = compute_resolution c l f s in
  (match result with
   | Nil -> Nil
   | Cons (_, _) -> append_to_list_of_ures (Mk_fcp (f, result)) s)
