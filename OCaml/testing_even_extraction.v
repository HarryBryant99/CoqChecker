Require Coq.extraction.Extraction.

Inductive even : nat -> Set :=
| even_0 : even O
| even_SS : forall n:nat, even n -> even (S (S n)).

Inductive even_prop : nat -> Prop :=
| even_prop_0 : even_prop O
| even_prop_SS : forall n:nat, even_prop n -> even_prop (S (S n)).

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.

Extraction "C:\Users\z004u5bh\Documents\Coq\OCaml\test.ml" even even_prop.