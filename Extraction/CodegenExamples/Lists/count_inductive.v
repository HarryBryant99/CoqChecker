Require Import codegen.codegen.

Require Import List.

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

CodeGen InductiveType list nat => "list_nat".
CodeGen InductiveMatch list nat => "list_nat_is_nil"
| nil => "default"
| cons => "case 0" "list_nat_head" "list_nat_tail".
CodeGen Constant nil nat => "((list_nat)NULL)".
CodeGen Primitive cons nat => "list_nat_cons".

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

CodeGen SourceFile "lists/count_inductive.c".
CodeGen StaticFunc lef.
CodeGen StaticFunc count.
CodeGen GenerateFile.