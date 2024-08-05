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

let string_of_clause clause =
  Printf.sprintf "[%s]" (string_of_list string_of_literal clause)

let string_of_proof_step = function
  | Ass n -> Printf.sprintf "Ass %s" (string_of_nat n)
  | Res (n1, n2, cl) -> Printf.sprintf "Res (%s, %s, %s)" (string_of_nat n1) (string_of_nat n2) (string_of_clause cl)

let string_of_proof = string_of_list string_of_proof_step

let string_of_assumptions = string_of_list string_of_clause

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

let string_of_clause clause =
  Printf.sprintf "[%s]" (string_of_list string_of_literal clause)

(* Convert a character to Coq ascii *)
let char_to_ascii c =
  let code = int_of_char c in
  let b7 = if code land 1 <> 0 then True else False in
  let b6 = if code land 2 <> 0 then True else False in
  let b5 = if code land 4 <> 0 then True else False in
  let b4 = if code land 8 <> 0 then True else False in
  let b3 = if code land 16 <> 0 then True else False in
  let b2 = if code land 32 <> 0 then True else False in
  let b1 = if code land 64 <> 0 then True else False in
  let b0 = if code land 128 <> 0 then True else False in
  Ascii (b0, b1, b2, b3, b4, b5, b6, b7)

(* Convert a string to Coq string *)
let rec string_to_coq_string s =
  if String.length s = 0 then EmptyString
  else String (char_to_ascii s.[0], string_to_coq_string (String.sub s 1 (String.length s - 1)))

(* Function to get user input *)
let get_user_input prompt =
  Printf.printf "%s" prompt;
  read_line ()

(* Function to create a literal from user input *)
let rec create_literal () =
  let str = get_user_input "Enter the string for the literal: " in
  Printf.printf "Enter 'p' for Positive or 'n' for Negative for the string \"%s\": " str;
  match read_line () with
  | "p" -> Pos (string_to_coq_string str)
  | "n" -> Neg (string_to_coq_string str)
  | _ -> Printf.printf "Invalid input. Please enter 'p' for Positive or 'n' for Negative.\n"; create_literal ()

(* Function to create a clause from user input *)
let create_clause () =
  let rec aux acc =
    let lit = create_literal () in
    match get_user_input "Do you want to add another literal to the clause? (y/n): " with
    | "y" -> aux (Cons (lit, acc))
    | "n" -> Cons (lit, acc) (* Add literal at the end *)
    | _ -> Printf.printf "Invalid input. Please enter 'y' or 'n'.\n"; aux acc
  in
  (* Reverse the order of literals here *)
  let reversed_clause = aux Nil in
  let rec reverse_list acc = function
    | Nil -> acc
    | Cons (x, xs) -> reverse_list (Cons (x, acc)) xs
  in reverse_list Nil reversed_clause

(* Function to create assumptions from user input *)
let create_assumptions () =
  let rec aux acc =
    let clause = create_clause () in
    match get_user_input "Do you want to add another clause? (y/n): " with
    | "y" -> aux (Cons (clause, acc)) (* Add clause at the end *)
    | "n" -> Cons (clause, acc) (* Add clause at the end *)
    | _ -> Printf.printf "Invalid input. Please enter 'y' or 'n'.\n"; aux acc
  in
  (* Reverse the order of clauses here *)
  let reversed_assumptions = aux Nil in
  let rec reverse_list acc = function
    | Nil -> acc
    | Cons (x, xs) -> reverse_list (Cons (x, acc)) xs
  in reverse_list Nil reversed_assumptions

(* Test functions *)
let test_isCorrect_example () =
  (* Create assumptions using the updated function *)
  let ass = create_assumptions () in
  
  (* Define a valid proof *)
  let p = Cons (Ass O, Cons (Ass (S O), Cons (Res (O, S O, Nil), Nil))) in

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
