Parameters A B : Set.

Inductive tree : Set := node : A -> forest -> tree

with forest : Set :=
| leaf : B -> forest
| cons : tree -> forest -> forest.

Check tree.
Check forest.

Check node.

Check leaf.
Check cons.


Inductive unitres :=
| subsumption : list -> unitres
| resolution : unitres -> unitres -> unitres

with list (A:Set) : Set :=
| nil : list A
| cons : A -> list A -> list A.