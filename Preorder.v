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
  | preordered_set_le_refl : forall set, preordered_set_le set set
  | preordered_set_le_allin : forall (set1 set2 : (A -> Prop)),
      (forall (x : A), set1 x -> set2 x) -> preordered_set_le set1 set2.
Arguments preordered_set_le {_}.

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

