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

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.
Extraction "/mnt/c/Users/z004u5bh/Documents/Coq/OCaml/opposite.ml" opposite.
