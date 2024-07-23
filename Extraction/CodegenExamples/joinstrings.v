Require Import codegen.codegen.
(*Require Import String.*)
Require Import Ascii.

Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

CodeGen InductiveType ascii => "unsigned char".
CodeGen Primitive Ascii => "make_char".

(*Open Scope string_scope.*)

Fixpoint eqb s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 && eqb s1' s2'
 | _,_ => false
 end.

Reserved Notation "x ++ y" (right associativity, at level 60).

Definition join a b := (a ++ b).

(*CodeGen Gen join.*)

Compute join "a" "b".

CodeGen SourceFile "Developments/joinstrings.c".

CodeGen Linear string.
CodeGen StaticFunc join.

CodeGen GenerateFile.