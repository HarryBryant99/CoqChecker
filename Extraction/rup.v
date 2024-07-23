Require Coq.extraction.Extraction.

(********************************)
(* Extraction Language: Haskell *)
(********************************)
Extraction Language Haskell.

(***************************)
(* Use Haskell basic types *)
(***************************)
Require Import ExtrHaskellBasic.

Require Import List.

Require Import PeanoNat.

Require Import String.
Open Scope string_scope.

Fixpoint eqb s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 && eqb s1' s2'
 | _,_ => false
 end.

Compute eqb "a" "!a".

Inductive list : Type :=
    | nil : list
    | cons : string -> list -> list.

  Infix "::" := cons (at level 60, right associativity) : list_scope.

  Open Scope list_scope.

Fixpoint already n l :=
match l with
nil => false
| a::tl =>
let r := already n tl in if eqb n a then true else r
end.

Compute already "A" ("B"::"a"::nil).

Fixpoint app (l m:list) {struct l} : list :=
    match l with
      | nil => m
      | a :: l1 => a :: app l1 m
    end.

Compute app ("a"::nil) ("b"::nil).

Fixpoint app_unique (l m:list) {struct l} : list :=
    match l with
      | nil => m
      | a :: l1 => if (already a m) then app_unique l1 m
                    else a :: app_unique l1 m
    end.

Compute app_unique ("a"::nil) ("a"::"b"::nil).

Fixpoint rup n l :=
match l with
nil => nil
| a::tl =>
let r := rup n tl in if eqb (append "!" a) n then r
  else if eqb (append "!" n) a then r
  (*else if eqb n a then r*)
  else (app (a::nil) r)
end.

Compute rup "aa" ("b"::"aa"::nil).

Fixpoint loop l n :=
match l with
nil => n
| a::tl => loop tl (rup a n)
end.

Compute loop ("aa"::"cz"::nil) ("c"::"aa"::nil).
Compute loop ("c"::"aa"::nil) ("aa"::"cz"::nil).

Definition clause b1 b2 : list :=
  app_unique (loop b1 b2) (loop b2 b1).


Compute clause ("a"::nil) ("a"::"b"::nil).

(*Extraction "rup.hs" app rup loop clause.*)