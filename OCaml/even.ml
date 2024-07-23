
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val even_double_equals_m : __ **)

let even_double_equals_m =
  __
