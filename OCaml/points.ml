type point =
  | NormalPoint
  | ReversePoint

let switch_point = function
  | NormalPoint -> ReversePoint
  | ReversePoint -> NormalPoint

let string_of_point = function
  | NormalPoint -> "NormalPoint"
  | ReversePoint -> "ReversePoint"

let () =
  let initial_point = NormalPoint in
  Printf.printf "Initial Point: %s\n" (string_of_point initial_point);
  let switched_point = switch_point initial_point in
  Printf.printf "Switched Point: %s\n" (string_of_point switched_point)
