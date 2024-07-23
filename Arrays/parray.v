Require Import codegen.codegen.

Require Import Array.PArray BinInt.
(*Require Import Int63.*)

Require Import Uint63.

Definition testArray : array nat := [| 0; 1; 2; 3 | 0 : nat |].

Compute testArray.

Definition charArray : array ch := [| 0; 1; 2; 3 | 0 : nat |].

Compute charArray.

CodeGen StaticArgs testArray "%array nat".

CodeGen Gen testArray.


Polymorphic Definition array_fold_right {A B : Type} (f: B -> A -> A) (a:A) (bs:array B) : A :=
  let size := length bs in
  fst (nat_rect (fun _ => (A*int)%type) (a,size-1)%int63
       (fun _ '(a',i)=> ( f (get bs i) a' ,pred i)) (Z.to_nat (Int63.to_Z size))).

Compute array_fold_right cons nil testArray.