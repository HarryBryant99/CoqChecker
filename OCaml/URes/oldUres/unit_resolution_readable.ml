type bool =
  | True
  | False

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

type clause =
  | Nilclause
  | Consclause of literal * clause

type formula =
  | Nilformula
  | Consformula of clause * formula

type unitres =
  | Subsumption of formula
  | Resolution of unitres * unitres

(** val opposite : literal -> literal **)

let opposite = function
| Pos s -> Neg s
| Neg s -> Pos s

(** val string_dec0 : string -> string -> bool **)

let string_dec0 s1 s2 =
  match string_dec s1 s2 with
  | Left -> True
  | Right -> False

(** val string_beq : string -> string -> bool **)

let string_beq =
  string_dec0

(** val literal_eqb : literal -> literal -> bool **)

let literal_eqb l1 l2 =
  match l1 with
  | Pos s1 -> (match l2 with
               | Pos s2 -> string_beq s1 s2
               | Neg _ -> False)
  | Neg s1 -> (match l2 with
               | Pos _ -> False
               | Neg s2 -> string_beq s1 s2)

(** val remlc : literal -> clause -> clause **)

let rec remlc l = function
| Nilclause -> Nilclause
| Consclause (l', ls) ->
  (match literal_eqb l l' with
   | True -> ls
   | False -> Consclause (l', (remlc l ls)))

(** val concat_clauses : clause -> clause -> clause **)

let rec concat_clauses c1 c2 =
  match c1 with
  | Nilclause -> c2
  | Consclause (l, ls) -> Consclause (l, (concat_clauses ls c2))

(** val nonEmptycla : clause -> bool **)

let nonEmptycla = function
| Nilclause -> False
| Consclause (_, _) -> True

(** val noEmptyFormula : formula -> bool **)

let rec noEmptyFormula = function
| Nilformula -> True
| Consformula (c, rest) ->
  (match nonEmptycla c with
   | True -> noEmptyFormula rest
   | False -> False)

(** val clause_eqb : clause -> clause -> bool **)

let rec clause_eqb c1 c2 =
  match c1 with
  | Nilclause ->
    (match c2 with
     | Nilclause -> True
     | Consclause (_, _) -> False)
  | Consclause (l1, ls1) ->
    (match c2 with
     | Nilclause -> False
     | Consclause (l2, ls2) ->
       (match literal_eqb l1 l2 with
        | True -> clause_eqb ls1 ls2
        | False -> False))

(** val remcf : clause -> formula -> formula **)

let rec remcf c = function
| Nilformula -> Nilformula
| Consformula (c', rest) ->
  (match clause_eqb c c' with
   | True -> remcf c rest
   | False -> Consformula (c', (remcf c rest)))

(** val has_single_literal : clause -> bool **)

let rec has_single_literal = function
| Nilclause -> False
| Consclause (_, c0) ->
  (match c0 with
   | Nilclause -> True
   | Consclause (_, _) -> False)

(** val remove_negated_literal : literal -> formula -> formula **)

let rec remove_negated_literal l = function
| Nilformula -> Nilformula
| Consformula (c, rest) ->
  let c' = remlc (opposite l) c in
  Consformula (c', (remove_negated_literal l rest))

(** val read_literal_from_clause : clause -> literal **)

let read_literal_from_clause = function
| Nilclause -> Pos EmptyString
| Consclause (l, _) -> l

(** val find_single_literal_clause : formula -> clause **)

let rec find_single_literal_clause = function
| Nilformula -> Nilclause
| Consformula (c, rest) ->
  (match has_single_literal c with
   | True -> c
   | False -> find_single_literal_clause rest)

(** val formula_eqb : formula -> formula -> bool **)

let rec formula_eqb f1 f2 =
  match f1 with
  | Nilformula ->
    (match f2 with
     | Nilformula -> True
     | Consformula (_, _) -> False)
  | Consformula (c1, rest1) ->
    (match f2 with
     | Nilformula -> False
     | Consformula (c2, rest2) ->
       (match clause_eqb c1 c2 with
        | True -> formula_eqb rest1 rest2
        | False -> False))

(** val contains_clause : formula -> clause -> bool **)

let rec contains_clause f cl =
  match f with
  | Nilformula -> False
  | Consformula (cl', rest) ->
    (match clause_eqb cl cl' with
     | True -> True
     | False -> contains_clause rest cl)

(** val add_unique_clauses : formula -> formula -> formula **)

let rec add_unique_clauses f1 f2 =
  match f1 with
  | Nilformula -> f2
  | Consformula (cl, rest) ->
    (match contains_clause f2 cl with
     | True -> add_unique_clauses rest f2
     | False -> add_unique_clauses rest (Consformula (cl, f2)))

(** val empty : formula **)

let empty =
  Nilformula

(** val process_formula : formula -> formula **)

let process_formula f =
  let found_clause = find_single_literal_clause f in
  let lit = read_literal_from_clause found_clause in
  let modified_formula = remove_negated_literal lit f in
  (match formula_eqb modified_formula f with
   | True -> f
   | False -> remcf found_clause modified_formula)

(** val formula_to_subsumption : formula -> unitres **)

let rec formula_to_subsumption f = match f with
| Nilformula -> Subsumption Nilformula
| Consformula (_, _) -> Subsumption (process_formula f)

(** val concat_formulas : formula -> formula -> formula **)

let rec concat_formulas f1 f2 =
  match f1 with
  | Nilformula -> f2
  | Consformula (c, rest) -> Consformula (c, (concat_formulas rest f2))

(** val readf : unitres -> formula **)

let rec readf = function
| Subsumption f -> f
| Resolution (u1, u2) -> concat_formulas (readf u1) (readf u2)

(** val resolve_two_unitres : unitres -> unitres -> unitres **)

let resolve_two_unitres u1 u2 =
  match u1 with
  | Subsumption f1 ->
    (match u2 with
     | Subsumption f2 ->
       Resolution ((Subsumption (process_formula (concat_formulas f1 f2))),
         (Subsumption Nilformula))
     | Resolution (_, _) ->
       let formula1 = readf u1 in
       let formula2 = readf u2 in
       let combined_formula =
         add_unique_clauses
           (process_formula (concat_formulas formula1 formula2)) empty
       in
       Resolution ((Subsumption combined_formula), (Subsumption Nilformula)))
  | Resolution (_, _) ->
    let formula1 = readf u1 in
    let formula2 = readf u2 in
    let combined_formula =
      add_unique_clauses
        (process_formula (concat_formulas formula1 formula2)) empty
    in
    Resolution ((Subsumption combined_formula), (Subsumption Nilformula))

(** val string_of_bool : bool -> string **)

let string_of_bool = function
  | True -> "True"
  | False -> "False"



(** val string_of_ascii : ascii -> string **)

let string_of_ascii = function
  | Ascii (b1, b2, b3, b4, b5, b6, b7, b8) ->
    let byte_value =
      (if b1 = True then 128 else 0) +
      (if b2 = True then 64 else 0) +
      (if b3 = True then 32 else 0) +
      (if b4 = True then 16 else 0) +
      (if b5 = True then 8 else 0) +
      (if b6 = True then 4 else 0) +
      (if b7 = True then 2 else 0) +
	  (if b8 = True then 1 else 0)
    in
    String.make 1 (Char.chr byte_value)
  
(** val string_of_string : string -> string **)

let rec string_of_string = function
  | EmptyString -> "EmptyString"
  | String (a, rest) -> "String (" ^ string_of_ascii a ^ ", " ^ string_of_string rest ^ ")"

(** val string_of_literal : literal -> string **)

let string_of_literal = function
  | Pos s -> "Pos " ^ string_of_string s
  | Neg s -> "Neg " ^ string_of_string s

(** val string_of_clause : clause -> string **)

let rec string_of_clause = function
  | Nilclause -> "Nilclause"
  | Consclause (l, ls) -> "Consclause (" ^ string_of_literal l ^ ", " ^ string_of_clause ls ^ ")"

(** val string_of_formula : formula -> string **)

let rec string_of_formula = function
  | Nilformula -> "Nilformula"
  | Consformula (c, rest) -> "Consformula (" ^ string_of_clause c ^ ", " ^ string_of_formula rest ^ ")"

(** val test_unit_resolution : unit -> unit **)

(** Define more test cases for the resolve_two_unitres function **)

(** Define more test cases for the resolve_two_unitres function **)

let test_resolve_two_unitres () =
  (* Test case 1: Two empty formulas *)
  let empty_formula = Nilformula in
  print_endline ("Formula 1 (Test case 1): " ^ string_of_formula empty_formula);
  let empty_subsumption = Subsumption empty_formula in
  print_endline ("Formula 2 (Test case 1): " ^ string_of_formula empty_formula);
  let result1 = resolve_two_unitres empty_subsumption empty_subsumption in

  print_endline (string_of_formula (readf result1));

  (* Test case 2: Two formulas with single clauses *)
  let literal_with_two_characters = Pos (String (Ascii (False, True, False, False, False, False, True, False), EmptyString)) in
 

  let clause1 = Consclause (Pos (String (Ascii (False, True, False, False, False, False, True, False), EmptyString)), Nilclause) in
  let clause2 = Consclause (Neg (String (Ascii (False, True, False, False, False, False, True, True), EmptyString)), Nilclause) in
  let formula1 = Consformula (clause1, Nilformula) in
  let formula2 = Consformula (clause2, Nilformula) in
  print_endline ("Formula 1 (Test case 2): " ^ string_of_formula formula1);
  print_endline ("Formula 2 (Test case 2): " ^ string_of_formula formula2);
  let subsumption1 = Subsumption formula1 in
  let subsumption2 = Subsumption formula2 in
  let result2 = resolve_two_unitres subsumption1 subsumption2 in
  
  print_endline (string_of_formula (readf result2));

  (* Add more test cases as needed *)
;;

test_resolve_two_unitres ();;



