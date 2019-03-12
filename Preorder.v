Require Import Coq.Arith.Arith.

Class PreorderedSet (X : Type) : Type :=
{
  preorder : X -> X -> Prop;
  preorder_refl: forall x, preorder x x;
  preorder_trans: forall x y z, preorder x y -> preorder y z -> preorder x z;
}.
Arguments Build_PreorderedSet X {_ _ _}.

Instance preorder_nat : PreorderedSet nat := 
{
  preorder := Nat.le;
  preorder_refl := Nat.le_refl;
  preorder_trans := Nat.le_trans;
}.

Inductive bool_le : bool -> bool -> Prop :=
  | bool_le_refl : forall b, bool_le b b.

Instance preorder_bool : PreorderedSet bool :=
{
  preorder := bool_le;
}.
- destruct x; constructor.
- destruct x, y, z; try constructor; tauto.
Defined.

Inductive preordered_set_le {A : Type} : (A -> Prop) -> (A -> Prop) -> Prop := 
  | preordered_set_le_allin : forall (set1 set2 : (A -> Prop)),
      (forall (x : A), set1 x -> set2 x) -> preordered_set_le set1 set2.
Arguments preordered_set_le {_}.

Lemma preordered_set_le_refl : forall {A:Type} (a : (A->Prop)),
  preordered_set_le a a.
Proof.
  intros. constructor. intros. assumption.
Qed.

Lemma preordered_set_le_trans : forall {A:Type} (x y z : (A->Prop)),
  preordered_set_le x y -> preordered_set_le y z -> preordered_set_le x z.
Proof. 
  intros. constructor. inversion H; inversion H0; subst; auto.
Qed.

Instance types_to_prop : forall (A : Type), PreorderedSet (A -> Prop) :=
{
  preorder := preordered_set_le;
  preorder_refl := preordered_set_le_refl;
  preorder_trans := preordered_set_le_trans;
}.
Arguments types_to_prop {A}.

Inductive pointwise_ordering {A A':Type} `{PreorderedSet A'} : 
  (A->A') -> (A->A') -> Prop :=
  | pointwise : forall (f1 f2 : (A->A')),
      (forall x, preorder (f1 x) (f2 x)) -> pointwise_ordering f1 f2.
      
Lemma pointwise_ordering_refl : 
  forall {A A':Type} `{PreorderedSet A'} (f : A -> A'),
  pointwise_ordering f f.
Proof. 
  intros A H f. constructor. intro x. apply preorder_refl.
Qed.

Lemma pointwise_ordering_trans : forall {A A': Type} `{PreorderedSet A'} 
  (f1 f2 f3 : A -> A'),
  pointwise_ordering f1 f2 -> pointwise_ordering f2 f3 -> 
  pointwise_ordering f1 f3.
Proof.
  intros A A' H f1 f2 f3. constructor. 
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  intro x. apply preorder_trans with (y:=(f2 x)); auto.
Qed.

Instance preordered_function_spaces : forall (A A' : Type), 
  PreorderedSet A' -> PreorderedSet (A->A')
:= {
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}. 

Instance preorder_endofunction : forall A,
  PreorderedSet A -> PreorderedSet (A->A)
:= {
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.

Lemma preorder_props : forall {X : Type} (P Q : X -> Prop) (x : X),
  preorder P Q -> P x -> Q x.
Proof. 
  intros. simpl in H. destruct H. apply H. apply H0.
Qed.


