(* ures_test.ml *)

(* Import the module containing the definitions. *)
open Ures

(* Define some helper functions for testing *)
let string_of_bool = function
  | True -> "True"
  | False -> "False"

let string_of_nat n =
  let rec aux n acc = match n with
    | O -> acc
    | S n' -> aux n' (acc + 1)
  in string_of_int (aux n 0)

let rec string_of_list string_of_elem = function
  | Nil -> "[]"
  | Cons (x, xs) -> Printf.sprintf "[%s] :: %s" (string_of_elem x) (string_of_list string_of_elem xs)

let char_of_ascii (Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) =
  let bit_to_int = function
    | True -> 1
    | False -> 0
  in
  Char.chr (
    bit_to_int b7 +
    (bit_to_int b6 lsl 1) +
    (bit_to_int b5 lsl 2) +
    (bit_to_int b4 lsl 3) +
    (bit_to_int b3 lsl 4) +
    (bit_to_int b2 lsl 5) +
    (bit_to_int b1 lsl 6) +
    (bit_to_int b0 lsl 7)
  )

let rec string_of_string = function
  | EmptyString -> ""
  | String (c, s) -> Printf.sprintf "%c%s" (char_of_ascii c) (string_of_string s)

let string_of_literal = function
  | Pos s -> Printf.sprintf "Pos \"%s\"" (string_of_string s)
  | Neg s -> Printf.sprintf "Neg \"%s\"" (string_of_string s)

let string_of_clause = string_of_list string_of_literal

let string_of_proof_step = function
  | Ass n -> Printf.sprintf "Ass %s" (string_of_nat n)
  | Res (n1, n2, cl) -> Printf.sprintf "Res (%s, %s, %s)" (string_of_nat n1) (string_of_nat n2) (string_of_clause cl)

let string_of_proof = string_of_list string_of_proof_step

let string_of_assumptions = string_of_list string_of_clause

(* Test functions *)
let test_isCorrect_example () =
  (* Define your assumptions and pre-proof *)
  let a = String (Ascii (False, True, True, False, False, False, False, True), EmptyString) in
  let b = String (Ascii (False, True, True, False, False, False, True, False), EmptyString) in

  let a0 = Cons (Pos a, Cons (Neg b, Nil)) in
  let a1 = Cons (Pos b, Nil) in
  let a2 = Cons (Neg a, Nil) in
  let ass = Cons (a0, Cons (a1, Cons (a2, Nil))) in

  let p = Cons (Ass O, Cons (Ass (S O), Cons (Ass (S (S O)), Cons (Res (O, S O, Cons (Pos a, Nil)), Cons (Res (S (S (S O)), S (S O), Nil), Nil))))) in

  (* Print the assumptions and proof *)
  Printf.printf "Assumptions: %s\n" (string_of_assumptions ass);
  Printf.printf "Proof: %s\n" (string_of_proof p);

  (* Call isCorrect *)
  let result = Ures.isCorrect ass p in

  (* Convert Ures.bool to bool and print the result *)
  let result_bool = match result with
    | Ures.True -> true
    | Ures.False -> false
  in
  Printf.printf "isCorrect result: %b\n" result_bool

(* Run the test *)
let () =
  test_isCorrect_example ()
