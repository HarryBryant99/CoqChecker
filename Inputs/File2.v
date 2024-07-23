(* In File2.v *)

(*coqc -Q /mnt/c/Users/z004u5bh/Documents/Coq/Inputs/ Test /mnt/c/Users/z004u5bh/Documents/Coq/Inputs/File1.v*)

Add LoadPath "/mnt/c/Users/z004u5bh/Documents/Coq/Inputs/" as Test.

From Test Require File1.

Print File1.A.
Print File1.example_def.

Check File1.A.



Add LoadPath "/mnt/c/Users/z004u5bh/Documents/Coq/Inductive/" as Inductive.
From Inductive Require CNFOp.


Check CNFOp.string_dec.


Require Import String.
Open Scope string_scope.

Compute CNFOp.string_dec "S" "A".

Check CNFOp.literal.