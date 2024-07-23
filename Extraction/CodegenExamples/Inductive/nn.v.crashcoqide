Require Import codegen.codegen.

Inductive nn :=
| O : nn
| S : nn -> nn.

Fixpoint add (n m: nn) : nn :=
  match n with 
  | O => m
  | S n' => S (add n' m)
end.

CodeGen Gen add.