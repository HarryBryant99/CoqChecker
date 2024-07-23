Require Import List.

Require Import codegen.codegen.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen InductiveType nat => "nat".
CodeGen InductiveMatch nat => ""
| O => "case 0"
| S => "default" "predn".
CodeGen Constant O => "0".
CodeGen Primitive S => "succn".
Print CodeGen Inductive nat.


CodeGen InductiveType (list nat) => "list_nat".
CodeGen InductiveMatch (list nat) => "sw_list_nat"
  | nil => "default"
  | cons => "case cons_nat_tag" "cons_nat_get_member_0" "cons_nat_get_member_1".
Print CodeGen Inductive (list nat).

Fixpoint lef (n m:nat) {struct m} : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n, S m => lef n m
  end.

Fixpoint count n l :=
match l with
nil => 0
| a::tl =>
let r := count n tl in if lef n a then 
  if lef a n then 1+r else r
  else r
end.

Compute count 2 (2::2::nil).

CodeGen Gen count lef.