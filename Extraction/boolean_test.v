Require Coq.extraction.Extraction.

(********************************)
(* Extraction Language: Haskell *)
(********************************)
Extraction Language Haskell.

(***************************)
(* Use Haskell basic types *)
(***************************)
Require Import ExtrHaskellBasic.

Definition aandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Extraction "And.hs" aandb. 