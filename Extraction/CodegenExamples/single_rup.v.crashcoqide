Require Import codegen.codegen.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Definition bool_eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition ascii_eqb (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    bool_eqb a0 b0 && bool_eqb a1 b1 && bool_eqb a2 b2 && bool_eqb a3 b3
    && bool_eqb a4 b4 && bool_eqb a5 b5 && bool_eqb a6 b6 && bool_eqb a7 b7
 end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(*CodeGen Gen andb.*)

Fixpoint compare s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => ascii_eqb c1 c2 && compare s1' s2'
 | _,_ => false
 end.

Reserved Notation "x ++ y" (right associativity, at level 60).

Fixpoint append (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (s1' ++ s2)
  end
where "s1 ++ s2" := (append s1 s2) : string_scope.

Definition join s1 s2 : string := if compare s1 s2 then s1 else append s1 s2.

Compute join "a" "b".

Definition rup s1 s2 neg : string := if compare (append neg s1) s2 then ""
  else if compare (append neg s2) s1 then ""
  else if compare s2 s1 then s1
  else (append s1 s2).

Compute rup "¬a" "a" "¬".

CodeGen SourceFile "strings/rup.c".
CodeGen StaticFunc compare.
CodeGen StaticFunc append.
CodeGen StaticFunc rup.
CodeGen GenerateFile.