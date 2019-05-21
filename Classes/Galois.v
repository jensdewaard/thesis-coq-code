Require Import PreorderedSet.

Class Galois (A B : Type) 
`{PreorderedSet B} : Type :=
{
  gamma : B -> A -> Prop;
  gamma_monotone : monotone gamma;

}.
Arguments Build_Galois A B {_ _ _}.
Arguments gamma {_ _ _ _}.
