Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.AbstractStore.
Require Import Language.Statements.
Require Import Types.Stores.

Definition abstract_store_join
  (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => VTop.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma abstract_store_join_comm : forall ast1 ast2,
  abstract_store_join ast1 ast2 = abstract_store_join ast2 ast1.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. reflexivity. 
Qed.

Lemma abstract_store_join_assoc : forall ast1 ast2 ast3,
  abstract_store_join ast1 (abstract_store_join ast2 ast3) =
  abstract_store_join (abstract_store_join ast1 ast2) ast3.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. reflexivity.
Qed.

Lemma abstract_store_join_upperbound_left :
    forall s s', preorder s (abstract_store_join s s').
Proof.
  simpl. unfold abstract_store_join. constructor.
  intro x. constructor.
Qed.

Lemma abstract_store_join_upperbound_right : 
  forall s s', preorder s' (abstract_store_join s s').
Proof.
  simpl. unfold abstract_store_join. constructor.
  intro x. constructor.
Qed.

Global Instance abstract_store_joinable : Joinable abstract_store := {
  join_op := abstract_store_join;
  join_upper_bound_left := abstract_store_join_upperbound_left;
  join_upper_bound_right := abstract_store_join_upperbound_right;
}.

