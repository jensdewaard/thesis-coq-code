Require Import Coq.Arith.Arith.

Class Proset (A : Type) : Type :=
{
  order : A -> A -> Prop;
  order_refl : forall x, order x x;
  order_trans : forall x y z, order x y -> order y z -> order x z;
}.
Arguments order {_ _}.

Arguments Build_Proset A {_ _ _}.


Class Poset (A : Type) `{Proset A} : Type :=
{
  order_antisym : forall x y, order x y -> order y x -> x = y;
}.
Arguments Build_Poset A {_ _}.
Print Poset.

Class TotalSet (A : Type) `{Proset A} : Type :=
{
  order_connex : forall x y, order x y /\ order y x;
}.

(* Instance proofs of the coq built-in datatypes *)

Instance proset_bool : Proset bool :=
{
  order := fun a b => a = b;
}.
- reflexivity.
- intros; subst; reflexivity.
Defined.

Print proset_bool.

Instance poset_bool : Poset bool.
Proof. 
  split. simpl. tauto.
Qed.

Instance proset_nat : Proset nat :=
{
  order := Nat.le;
  order_refl := Nat.le_refl;
  order_trans := Nat.le_trans;
}.

