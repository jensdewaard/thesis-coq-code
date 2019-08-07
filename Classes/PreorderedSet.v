Require Import Coq.Classes.RelationClasses.

Class PreorderedSet (X : Type) : Type :=
{
  preorder : X -> X -> Prop;
  preorder_refl: Reflexive preorder;
  preorder_trans: Transitive preorder;
}.

Arguments Build_PreorderedSet X {_ _ _}.

Definition monotone {A A'} `{PreorderedSet A, PreorderedSet A'} :
  (A -> A') -> Prop :=
  fun f => forall (a a': A), preorder a a' -> preorder (f a) (f a').
  
