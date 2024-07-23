Require Import codegen.codegen.

CodeGen InductiveType nat => "nat".
CodeGen InductiveMatch nat => ""
| O => "case 0"
| S => "default" "predn".
CodeGen Constant O => "0".
CodeGen Primitive S => "succn".
Print CodeGen Inductive nat.

Fixpoint lef (n m:nat) {struct m} : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n, S m => lef n m
  end.

Fixpoint my_add n m :=
  match n with
  | 0 => m
  | S p => my_add p (S m)
  end.

Compute my_add 2 3.

(*Extraction "my_add.hs" my_add.*)

Fixpoint div x y := match x with
| 0 => 0
| S x' =>
let z := div x' y in
if (S z)*y lef x then S z else z
end.

(*Extraction "div.ml" div.*)
(*Extraction "div.hs" div.*)

CodeGen Gen my_add.