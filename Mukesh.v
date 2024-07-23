Require Import List.
Import ListNotations. 

Definition square_of_nat (n : nat) : nat := n * n.
Theorem square_nat : forall (n : nat), square_of_nat n = n * n.
Proof.
  reflexivity.
Qed.


Fixpoint reverse_list {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t =>
      let ret := reverse_list t in
      ret ++ [h]
  end.
 
Eval compute in reverse_list [1; 2; 3]. 
From Coq Require Extraction.
Recursive Extraction reverse_list.
 
(*
type 'a list =
| Nil
| Cons of 'a * 'a list
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)
let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m)) 

(** val reverse_list : 'a1 list -> 'a1 list **)

let rec reverse_list = function
| Nil -> Nil
| Cons (h, t) -> let ret = reverse_list t in app ret (Cons (h, Nil))

*)