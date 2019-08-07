Require Import Maps.
Require Import Types.Parity.
Require Import Language.Statements.

Definition store := total_map cvalue.
Definition abstract_store := total_map avalue.

Definition abstract_store_top : abstract_store :=
  fun _ => VTop.
Definition abstract_store_bottom : abstract_store :=
  fun _ => VBottom.
Definition abstract_store_join
    (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => VTop.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma abstract_store_join_comm : forall ast1 ast2,
  abstract_store_join ast1 ast2 = abstract_store_join ast2 ast1.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. reflexivity. Qed.

Lemma abstract_store_join_assoc : forall ast1 ast2 ast3,
  abstract_store_join ast1 (abstract_store_join ast2 ast3) =
  abstract_store_join (abstract_store_join ast1 ast2) ast3.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. reflexivity.
Qed.


