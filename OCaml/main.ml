(* main.ml *)

(* Import Opposite module *)
module Opposite = Opposite

let rec string_of_literal = function
  | Opposite.Pos s -> "Pos " ^ string_of_string s
  | Opposite.Neg s -> "Neg " ^ string_of_string s

and string_of_string = function
  | Opposite.EmptyString -> "EmptyString"
  | Opposite.String (a, rest) ->
      "String (" ^ string_of_ascii a ^ ", " ^ string_of_string rest ^ ")"

and string_of_ascii = function
  | Opposite.Ascii (b1, b2, b3, b4, b5, b6, b7, b8) ->
      "Ascii (" ^
      string_of_bool b1 ^ ", " ^
      string_of_bool b2 ^ ", " ^
      string_of_bool b3 ^ ", " ^
      string_of_bool b4 ^ ", " ^
      string_of_bool b5 ^ ", " ^
      string_of_bool b6 ^ ", " ^
      string_of_bool b7 ^ ", " ^
      string_of_bool b8 ^ ")"

and string_of_bool = function
  | Opposite.True -> "True"
  | Opposite.False -> "False"

let main () =
  let sample_literal = Opposite.Pos (Opposite.String (Opposite.Ascii (Opposite.True, Opposite.False, Opposite.True, Opposite.False, Opposite.True, Opposite.False, Opposite.True, Opposite.False), Opposite.EmptyString)) in
  print_endline ("Original literal: " ^ string_of_literal sample_literal);

  let opposite_literal_result = Opposite.opposite sample_literal in
  print_endline ("Opposite literal: " ^ string_of_literal opposite_literal_result)

let () = main ()

