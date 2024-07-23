type bool =
  | True
  | False

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
  | EmptyString
  | String of ascii * string

type literal =
  | Pos of string
  | Neg of string

let opposite = function
  | Pos s -> Neg s
  | Neg s -> Pos s

let rec string_of_literal = function
  | Pos s -> "Pos " ^ string_of_string s
  | Neg s -> "Neg " ^ string_of_string s

and string_of_string = function
  | EmptyString -> "EmptyString"
  | String (a, rest) -> "String (" ^ string_of_ascii a ^ ", " ^ string_of_string rest ^ ")"

and string_of_ascii = function
  | Ascii (b1, b2, b3, b4, b5, b6, b7, b8) ->
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
  | True -> "True"
  | False -> "False"

let () =
  let sample_literal = Pos (String (Ascii (True, False, True, False, True, False, True, False), EmptyString)) in
  print_endline ("Original literal: " ^ string_of_literal sample_literal);

  let opposite_literal = opposite sample_literal in
  print_endline ("Opposite literal: " ^ string_of_literal opposite_literal)

