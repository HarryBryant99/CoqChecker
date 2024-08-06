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
  | Cons (x, xs) -> Printf.sprintf "%s :: %s" (string_of_elem x) (string_of_list string_of_elem xs)

let string_of_ascii (Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) =
  let string_of_bit = function
    | True -> "1"
    | False -> "0"
  in Printf.sprintf "%s%s%s%s%s%s%s%s"
       (string_of_bit b0) (string_of_bit b1) (string_of_bit b2) (string_of_bit b3)
       (string_of_bit b4) (string_of_bit b5) (string_of_bit b6) (string_of_bit b7)

let rec string_of_string = function
  | EmptyString -> ""
  | String (c, s) -> Printf.sprintf "%s%s" (string_of_ascii c) (string_of_string s)

let string_of_literal = function
  | Pos s -> Printf.sprintf "Pos %s" (string_of_string s)
  | Neg s -> Printf.sprintf "Neg %s" (string_of_string s)

let string_of_clause = string_of_list string_of_literal

(* Test functions *)
let test_isCorrect () =
  (* Define your assumptions and pre-proof *)
  let a1 = Cons (Pos (String (Ascii (True, False, True, False, True, False, True, False), EmptyString)), Nil) in
  let a2 = Cons (Neg (String (Ascii (True, False, True, False, True, False, True, False), EmptyString)), Nil) in
  let ass = Cons (a1, Cons (a2, Nil)) in
  let p = Cons (Ass O, Cons (Ass (S O), Cons (Res (O, S O, Nil), Nil))) in

  (* Call isCorrect *)
  let result = Ures.isCorrect ass p in

  (* Convert Ures.bool to bool and print the result *)
  let result_bool = match result with
    | Ures.True -> true
    | Ures.False -> false
  in
  Printf.printf "isCorrect result: %b\n" result_bool

(*incorrect*)  
let test_isCorrect_fail () =
  (* Define your assumptions and pre-proof *)
  let a1 = Cons (Pos (String (Ascii (True, False, True, False, True, False, True, False), EmptyString)), Nil) in
  let a2 = Cons (Neg (String (Ascii (True, False, True, False, True, False, True, False), EmptyString)), Nil) in
  let ass = Cons (a1, Cons (a2, Nil)) in
  let p = Cons (Ass O, Cons (Ass (S O), Cons (Res (O, S O, a1), Nil))) in

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
  test_isCorrect ();
  test_isCorrect_fail ()
