type bool =
  | True
  | False

type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
  | EmptyString
  | String of ascii * string

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, append s1' s2)

let concatenate_strings = append

let rec result_to_string = function
  | EmptyString -> ""
  | String (Ascii (b1, b2, b3, b4, b5, b6, b7, b8), rest) ->
    let char_of_bool = function
      | True -> '1'
      | False -> '0'
    in
    Char.escaped (Char.chr (int_of_string ("0b" ^
      String.concat "" (List.map (fun b -> char_of_bool b |> String.make 1) [b1; b2; b3; b4; b5; b6; b7; b8])
    ))) ^ result_to_string rest

let () =
  let s1 = String (Ascii (True, False, True, False, True, False, True, False), EmptyString) in
  let s2 = String (Ascii (False, True, False, True, False, True, False, True), EmptyString) in
  let result = concatenate_strings s1 s2 in
  print_endline ("Concatenated string: " ^ result_to_string result)

