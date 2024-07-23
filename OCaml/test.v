Require Coq.extraction.Extraction.

Require Import Coq.Strings.String.

(* Define a simple function in Coq *)
Definition concatenate_strings (s1 s2 : string) : string :=
  append s1 s2.

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.
Extraction "/mnt/c/Users/z004u5bh/Documents/Coq/OCaml/example.ml" concatenate_strings.
