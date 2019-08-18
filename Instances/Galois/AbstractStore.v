Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Instances.Galois.Values.
Require Import Instances.Preorder.AbstractStore.
Require Import Types.Stores.

Definition gamma_store : abstract_store -> store -> Prop :=
  fun st' => fun st => forall x, gamma (st' x) (st x).

Definition gamma_store_monotone : monotone gamma_store.
Proof. unfold monotone.
  intros ast ast'. simpl. constructor. intros st. unfold gamma_store in *. 
  intros Hgamma x. destruct H. eapply widen. apply H. apply Hgamma.
Qed.

Global Instance galois_store : Galois store abstract_store :=
{
  gamma := gamma_store;
  gamma_monotone := gamma_store_monotone;
}.
