Require Import ZArith.
Open Scope Z_scope.

Lemma iter_nat_of_Z : forall n A (f : A -> A) x, 0 <= n ->
Z.iter n f x = iter_nat (Zabs_nat n) A f x.