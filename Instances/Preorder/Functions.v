Require Import Coq.Classes.RelationClasses.

Require Import Classes.PreorderedSet.

Section preordered_functions.
Context {A A' : Type} `{PreorderedSet A'}.

Inductive pointwise_ordering : 
  (A->A') -> (A->A') -> Prop :=
  | pointwise : forall (f1 f2 : (A->A')),
      (forall x, preorder (f1 x) (f2 x)) -> pointwise_ordering f1 f2.

Lemma pointwise_ordering_refl : 
  Reflexive pointwise_ordering.
Proof. 
  intros f. constructor. intro x. apply preorder_refl.
Qed.

Lemma pointwise_ordering_trans : 
  Transitive pointwise_ordering.
Proof.
  constructor.
  intros. 
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  eapply preorder_trans. apply H2. apply H0.
Qed.

Global Instance preordered_function_spaces : 
  PreorderedSet (A->A') :=
{
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.
  
End preordered_functions.
