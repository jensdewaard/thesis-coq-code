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
  
Section preordered_sets_le.
Context {A : Type}.

Inductive preordered_set_le : (A -> Prop) -> (A -> Prop) -> Prop := 
  | preordered_set_le_allin : forall (set1 set2 : (A -> Prop)),
      (forall (x : A), set1 x -> set2 x) -> preordered_set_le set1 set2.

Lemma preordered_set_le_refl : forall (a : (A->Prop)),
  preordered_set_le a a.
Proof.
  intros. constructor. intros. assumption.
Qed.

Lemma preordered_set_le_trans : forall (x y z : (A->Prop)),
  preordered_set_le x y -> preordered_set_le y z -> preordered_set_le x z.
Proof. 
  intros. constructor. inversion H; inversion H0; subst; auto.
Qed.

Global Instance types_to_prop : PreorderedSet (A -> Prop) :=
{
  preorder := preordered_set_le;
  preorder_refl := preordered_set_le_refl;
  preorder_trans := preordered_set_le_trans;
}.

End preordered_sets_le.
