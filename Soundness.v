Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractBool.
Require Import AbstractStore.
Require Import AbstractInterpreter.
Require Import Aux.
Require Import ConcreteInterpreter.
Require Import Galois.
Require Import Language.
Require Import Maps.
Require Import Parity.
Require Import Preorder.
Open Scope com_scope.

Definition sound {A B A' B' : Type} 
  `{Galois A B} `{Galois A' B'}
  (f : A->A') (f' : B->B') :=
  forall b a, gamma b a -> gamma (f' b) (f a).

Lemma sound_parity_plus :
  sound plus parity_plus.
Proof.
  unfold sound. simpl. unfold gamma_fun; intros. simpl. 
  destruct b, b0; simpl in *; try tauto;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.

Lemma sound_parity_mult :
  sound mult parity_mult.
Proof. 
  unfold sound. simpl. unfold gamma_fun. intros. simpl.
  destruct b, b0; simpl in *; try tauto; 
  auto using even_mult_l, even_mult_r, odd_mult.
Qed.

Lemma sound_parity_eq :
  sound Nat.eqb parity_eq.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, b0; simpl in *; try tauto; unfold not; intros.
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd. 
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd.
Qed.

Lemma sound_ab_and :
  sound andb and_ab.
Proof. 
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.

Lemma sound_ab_or :
  sound orb or_ab.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.

Lemma sound_ab_neg :
  sound negb neg_ab.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, a; simpl in *; tauto.
Qed.

