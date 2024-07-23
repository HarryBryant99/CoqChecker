Require Import codegen.codegen.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

Definition aandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => b1
  end.
Example test_aandb1: (aandb true true) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_aandb2: (aandb true false) = false.
simpl.
reflexivity.
Qed.

Example test_aandb3: (aandb false true) = false.
simpl.
reflexivity.
Qed.

Example test_aandb4: (aandb false false) = false.
Proof.
simpl.
reflexivity.
Qed.

Compute aandb true true.
Compute aandb true false.
Compute aandb false true.
Compute aandb false false.

CodeGen Gen aandb.