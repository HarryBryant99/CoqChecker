Require Import codegen.codegen.

Require Import List.

Require Import Ascii.
Require Import String.
Open Scope string_scope.

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

CodeGen InductiveType list string => "list_string".
CodeGen InductiveMatch list string => "list_string_is_nil"
| nil => "default"
| cons => "case 0" "list_string_head" "list_string_tail".
CodeGen Constant nil string => "((list_string)NULL)".
CodeGen Primitive cons string => "list_string_cons".

Definition bool_eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition ascii_eqb (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    bool_eqb a0 b0 && bool_eqb a1 b1 && bool_eqb a2 b2 && bool_eqb a3 b3
    && bool_eqb a4 b4 && bool_eqb a5 b5 && bool_eqb a6 b6 && bool_eqb a7 b7
 end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(*CodeGen Gen andb.*)

Fixpoint compare s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => ascii_eqb c1 c2 && compare s1' s2'
 | _,_ => false
 end.

Fixpoint count n l :=
match l with
nil => 0
| a::tl =>
let r := count n tl in if compare n a then 1+r else r
end.

Compute count "a" ("a"::"a"::nil).

CodeGen SourceFile "lists/count_string.c".
CodeGen StaticFunc compare.
CodeGen StaticFunc count.
CodeGen GenerateFile.