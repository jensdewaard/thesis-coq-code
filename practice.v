Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractState.
Require Import AbstractInterpreter.
Require Import Aux.
Require Import ConcreteInterpreter.
Require Import Parity.
Require Import Maps.
Require Import Language.

Open Scope com_scope.

Lemma abstract_aexp_plus_sound : forall e1 e2,
  sound_aexp e1 ->
  sound_aexp e2 ->
  sound_aexp (APlus e1 e2).
Proof. 
  unfold sound_aexp. intros. simpl. apply parity_plus_sound. 
  apply H. assumption.
  apply H0. assumption.
Qed.

Lemma abstract_aexp_mult_sound : forall e1 e2,
  sound_aexp e1 ->
  sound_aexp e2 ->
  sound_aexp (AMult e1 e2).
Proof.
  unfold sound_aexp. intros. apply parity_mult_sound. apply H. assumption.
  apply H0. assumption. Qed.

Lemma abstract_aexp_var_sound : forall x,
  sound_aexp (AVar x).
Proof. intros. unfold sound_aexp. intros. simpl. unfold sound_state in H.
  apply H. Qed.


Theorem abstract_aexp_eval_sound : forall e,
  sound_aexp e.
Proof. 
  induction e; intros.
  - (* ANum *) unfold sound_aexp. intros. simpl. apply gamma_extract_n_n.
  - (* AVar *) apply abstract_aexp_var_sound. 
  - (* APlus *) apply abstract_aexp_plus_sound; auto.
  - (* AMult *) apply abstract_aexp_mult_sound; auto.
Qed.

Lemma abstract_ceval_ass_sound : forall y a,
  sound_com (y ::= a).
Proof.
  unfold sound_com. 
  intros. simpl. unfold t_update, sound_state. intros.
  destruct (beq_string y x). 
  - apply abstract_aexp_eval_sound. apply H.
  - unfold sound_state in H. apply H.
Qed.

Lemma abstract_ceval_seq_sound : forall c1 c2,
  sound_com c1 ->
  sound_com c2 ->
  sound_com (c1 ;; c2).
Proof. 
  unfold sound_com. intros. apply H0. apply H. assumption.
Qed.

Theorem abstract_ceval_sound : forall c,
  sound_com c.
Proof. 
  intros c. induction c; intros.
  - (* SKIP *) unfold sound_com. simpl. intros. assumption.
  - (* CSeq *) apply abstract_ceval_seq_sound; assumption.
  - apply abstract_ceval_ass_sound.
Qed.

