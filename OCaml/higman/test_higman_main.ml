(* test_higman_main.ml *)

(* Include the modules from higman.ml *)
include Higman

let rec string_of_letter = function
  | A -> "A"
  | B -> "B"

let rec string_of_word = function
  | Nil -> ""
  | Cons (letter, rest) -> string_of_letter letter ^ string_of_word rest

let rec print_words_list = function
  | Nil -> ()
  | Cons (w, rest) ->
    print_string (string_of_word w ^ " ");
    print_words_list rest

(* Convert nat to int *)
let rec nat_to_int = function
  | O -> 0
  | S n' -> 1 + nat_to_int n'
  
let rec int_to_nat = function
  | 0 -> O
  | n -> S (int_to_nat (n - 1))
  
let () =
  let print_test_result prefix =
    print_string "Test Result: ";
    print_words_list prefix;
    print_newline ()
  in

  (* Test case 1 *)
  let prefix1 = good_prefix (fun _ -> Nil) in
  print_test_result prefix1;

  (* Test case 2 *)
  let prefix2 = good_prefix (fun n -> Cons (A, Cons (B, Nil))) in
  print_test_result prefix2;

  (* Test case 3 *)
  let prefix3 = good_prefix (fun n -> Cons (B, Cons (A, Nil))) in
  print_test_result prefix3;
  
  (* Test case 4: Prefix with letter "B" *)
  let prefix4 = good_prefix (fun n -> Cons (B, Nil)) in
  print_test_result prefix4;
  
  (* Test case 5: Prefix with alternating "ABAB" pattern *)
  let prefix5 = good_prefix (fun n -> Cons (A, Cons (B, Cons (A, Cons (B, Nil))))) in
  print_test_result prefix5;

  (* Test case 6: Prefix with alternating "BABABA" pattern *)
  let prefix6 = good_prefix (fun n -> Cons (B, Cons (A, Cons (B, Cons (A, Cons (B, Cons (A, Nil))))))) in
  print_test_result prefix6;