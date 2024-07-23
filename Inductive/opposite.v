Require Import Bool.
Require Import String.
Open Scope string_scope.

Require Import codegen.codegen.

Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen InductiveType literal => "literal".


Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

(*
CodeGen Gen opposite.
*)

(*
CodeGen HeaderFile "ures/opposite_gen.h".
*)
CodeGen SourceFile "ures/opposite_gen.c".
CodeGen StaticFunc opposite.
CodeGen GenerateFile.