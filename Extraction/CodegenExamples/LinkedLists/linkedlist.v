Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Arith.
Module Import M := FMapList.Make(Nat_as_OT).

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

Inductive LinkedList : Type :=
  | node (self: nat) (n: nat).

Definition memory : Type := M.t LinkedList.

Definition new (m : memory) : LinkedList * memory :=
  let elem := node (1 + cardinal m) 0 in 
  (elem, (add (1 + cardinal m) elem m)).


Definition is_empty (m: memory) (l: LinkedList) : bool :=
  match l with node _ n => 
      match (find n m) with 
      | Some _ => false
      | None => true 
      end
  end.

Definition push (m: memory) (l: LinkedList) (item: nat) :=
  match l with
  | node s n => ((add item (node item n) m), node s item)
  end.

Definition pop (m: memory) (l: LinkedList) :=
  match (is_empty m l) with
  | true => None
  | false => match l with
             | node s n => Some n
             end
  end.

CodeGen Linear LinkedList.
CodeGen InductiveType LinkedList => "LinkedList".

CodeGen Func push.
CodeGen Gen "push".