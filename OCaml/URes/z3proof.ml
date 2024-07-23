open Ures

(* Utility function to convert a char to an Ascii representation *)
let char_to_ascii c =
  let code = Char.code c in
  Ascii (
    (if code land 0b10000000 <> 0 then True else False),
    (if code land 0b01000000 <> 0 then True else False),
    (if code land 0b00100000 <> 0 then True else False),
    (if code land 0b00010000 <> 0 then True else False),
    (if code land 0b00001000 <> 0 then True else False),
    (if code land 0b00000100 <> 0 then True else False),
    (if code land 0b00000010 <> 0 then True else False),
    (if code land 0b00000001 <> 0 then True else False)
  )

(* Utility function to convert a string to a list of Ascii representations *)
let rec string_to_ascii_list = function
  | "" -> EmptyString
  | s -> String (char_to_ascii s.[0], string_to_ascii_list (String.sub s 1 (String.length s - 1)))

(* Utility function to create a literal from a string *)
let create_literal s =
  if String.get s 0 = '~' then
    Neg (string_to_ascii_list (String.sub s 1 (String.length s - 1)))
  else
    Pos (string_to_ascii_list s)

(* Custom function to get the head of a custom list *)
let hd = function
  | Nil -> failwith "Empty list"
  | Cons (x, _) -> x

(* Utility functions to convert custom types to strings for printing *)
let bool_to_string = function
  | True -> "True"
  | False -> "False"

(* Convert an Ascii representation to a char *)
let ascii_to_char (Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) =
  let bool_to_int = function True -> 1 | False -> 0 in
  let char_code = (bool_to_int b0 lsl 7) lor (bool_to_int b1 lsl 6) lor (bool_to_int b2 lsl 5) lor
                  (bool_to_int b3 lsl 4) lor (bool_to_int b4 lsl 3) lor (bool_to_int b5 lsl 2) lor
                  (bool_to_int b6 lsl 1) lor (bool_to_int b7) in
  Char.chr char_code

(* Convert a string representation back to a readable string *)
let rec ascii_list_to_string = function
  | EmptyString -> ""
  | String (a, s) -> (String.make 1 (ascii_to_char a)) ^ (ascii_list_to_string s)

let literal_to_string = function
  | Pos s -> Printf.sprintf "Pos (%s)" (ascii_list_to_string s)
  | Neg s -> Printf.sprintf "Neg (%s)" (ascii_list_to_string s)

let rec list_to_string f = function
  | Nil -> "Nil"
  | Cons (x, xs) -> Printf.sprintf "Cons (%s, %s)" (f x) (list_to_string f xs)

let clause_to_string = list_to_string literal_to_string
let formula_to_string = list_to_string clause_to_string

let formula_clause_pair_to_string (Mk_fcp (f, c)) =
  Printf.sprintf "Mk_fcp (%s, %s)" (formula_to_string f) (clause_to_string c)

let list_of_ures_to_string = list_to_string formula_clause_pair_to_string

(* Test cases *)
let test_resolution () =
  let x' = create_literal "~x" in
  let x = create_literal "x" in
  let y' = create_literal "y" in
  let y = create_literal "~y" in
  let z' = create_literal "z" in
  let z = create_literal "~z" in  
  
  let c1 = Cons (z', Nil) in
  let c2 = Cons (y, Cons(z, Nil)) in
  let c3 = Cons (x', Cons(y, Cons(z, Nil))) in
  let c4 = Cons (x, Cons(y', Nil)) in
  let f = Cons (c1, Cons(c2, Cons(c3, Cons(c4, Nil)))) in
  
  let s1 = compute_subsumption c1 c1 f Nil in
  let s2 = compute_subsumption c2 c2 f s1 in

  let r1 = compute_resolution c2 z f s2 in
  let s3 = is_resolution_complete c2 z f s2 in
  print_endline ("Result of r1: " ^ clause_to_string r1);
  print_endline ("Result of ures1: " ^ list_of_ures_to_string s3);
  
  let s4 = compute_subsumption c3 c3 f s2 in
  let s5 = compute_subsumption c4 c4 f s3 in
  
  let r2 = compute_resolution c4 y' f s5 in
  let s6 = is_resolution_complete c2 z f s2 in
  print_endline ("Result of r2: " ^ clause_to_string r2);
  print_endline ("Result of ures2: " ^ list_of_ures_to_string s6)

(* Run the test *)
let () = test_resolution ()