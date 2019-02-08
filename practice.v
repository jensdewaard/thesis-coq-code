Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractBool.
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

Lemma abstract_beval_eq_sound : forall a1 a2,
  sound_bexp (BEq a1 a2).
Proof.
  unfold sound_bexp. intros. simpl. pose proof abstract_aexp_eval_sound. 
  unfold sound_aexp in H0. assert (sound_par (abstract_eval_aexp ast a1)
  (eval_aexp st a1)).
  { apply H0. assumption. }
  assert (sound_par (abstract_eval_aexp ast a2) (eval_aexp st a2)).
  { apply H0. assumption. }
  clear H0. 
  destruct (abstract_eval_aexp ast a1) eqn:Ha1; 
  destruct (abstract_eval_aexp ast a2) eqn:Ha2; try reflexivity; simpl in *.
  - destruct (Nat.eqb (eval_aexp st a1) (eval_aexp st a2)) eqn:Heq; 
    try reflexivity.
    pose proof not_even_and_odd. apply Nat.eqb_eq in Heq. rewrite Heq in H1.
    simpl. apply H0 with (n:=(eval_aexp st a2)); assumption.
  - destruct (Nat.eqb (eval_aexp st a1) (eval_aexp st a2)) eqn:Heq;
    try reflexivity.
    pose proof not_even_and_odd. apply Nat.eqb_eq in Heq. rewrite Heq in H1.
    simpl. apply H0 with (n:=(eval_aexp st a2)); assumption.
Qed.

Theorem abstract_beval_sound : forall e,
  sound_bexp e.
Proof. 
  unfold sound_bexp. intros. induction e; try reflexivity.
  - apply abstract_beval_eq_sound. assumption. 
  - simpl. apply neg_ab_sound. assumption.
  - simpl. apply and_ab_sound. assumption. assumption.
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

