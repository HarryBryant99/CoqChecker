
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

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

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

(** val literal_eq_dec : literal -> literal -> sumbool **)

let literal_eq_dec l1 l2 =
  match l1 with
  | Pos s -> (match l2 with
              | Pos s0 -> string_dec s s0
              | Neg _ -> Right)
  | Neg s -> (match l2 with
              | Pos _ -> Right
              | Neg s0 -> string_dec s s0)

(** val literal_eq : literal -> literal -> bool **)

let rec literal_eq l1 l2 =
  match l1 with
  | Pos s1 ->
    (match l2 with
     | Pos s2 -> (match string_dec s1 s2 with
                  | Left -> True
                  | Right -> False)
     | Neg _ -> False)
  | Neg s1 ->
    (match l2 with
     | Pos _ -> False
     | Neg s2 -> (match string_dec s1 s2 with
                  | Left -> True
                  | Right -> False))

(** val clause_eq_dec : clause -> clause -> bool **)

let rec clause_eq_dec c1 c2 =
  match c1 with
  | Nil -> (match c2 with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (x, xs) ->
    (match c2 with
     | Nil -> False
     | Cons (y, ys) ->
       (match literal_eq_dec x y with
        | Left -> clause_eq_dec xs ys
        | Right -> False))

(** val memcf : clause -> formula -> bool **)

let rec memcf a = function
| Nil -> False
| Cons (b, m) ->
  (match clause_eq_dec a b with
   | True -> True
   | False -> memcf a m)

(** val inb : literal -> clause -> bool **)

let rec inb l = function
| Nil -> False
| Cons (x, xs) -> (match literal_eq l x with
                   | True -> True
                   | False -> inb l xs)

(** val subset : clause -> clause -> bool **)

let subset c1 c2 =
  forallb (fun l -> inb l c2) c1

type formula_clause_pair =
| Mk_fcp of formula * clause

type list_of_ures = formula_clause_pair list

(** val check_subsumption : clause -> clause -> formula -> bool **)

let check_subsumption c c2 f =
  match memcf c f with
  | True -> subset c c2
  | False -> False

(** val append_to_list_of_ures :
    formula_clause_pair -> list_of_ures -> list_of_ures **)

let append_to_list_of_ures n s =
  Cons (n, s)

(** val compute_subsumption :
    clause -> clause -> formula -> list_of_ures -> list_of_ures **)

let compute_subsumption c c2 f s =
  match check_subsumption c c2 f with
  | True -> append_to_list_of_ures (Mk_fcp (f, c2)) s
  | False -> s
