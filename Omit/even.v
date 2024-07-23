Inductive even : nat -> Set :=
| even_0 : even O
| even_SS : forall n:nat, even n -> even (S (S n)).

Definition even_dec : forall s1 s2 : even, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Defined.

Definition compare_even (a b : even) : bool :=
  if even_dec a b then true else false.

Definition isTwo n even : bool :=
if n 