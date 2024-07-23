Require Coq.extraction.Extraction.

Require Import String.
Open Scope string_scope.

Require Import codegen.codegen.

Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

Definition transform_literal (prefix : string) (L : literal) : literal :=
  match L with
  | pos s => pos (prefix ++ s)
  | neg s => neg (prefix ++ s)
  end.

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.
Extraction "/mnt/c/Users/z004u5bh/Documents/Coq/OCaml/opposite2.ml" opposite transform_literal.
