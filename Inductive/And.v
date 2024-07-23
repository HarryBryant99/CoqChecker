Require Import codegen.codegen.

Inductive bool : Set :=
  | true : bool
  | false : bool.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_andb_true_true : andb true true = true.
Proof. reflexivity. Qed.

Example test_andb_true_false : andb true false = false.
Proof. reflexivity. Qed.

Example test_orb_true_false : orb true false = true.
Proof. reflexivity. Qed.

CodeGen SourceFile "and/and.c".
CodeGen StaticFunc andb.
CodeGen StaticFunc orb.
CodeGen GenerateFile.