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

Definition state := total_map nat.

Definition abstract_state := total_map (parity).

Open Scope com_scope.

Lemma abstract_aexp_plus_sound : forall st ast e1 e2,
  gamma_par (abstract_eval_aexp ast e1) (eval_aexp st e1) ->
  gamma_par (abstract_eval_aexp ast e2) (eval_aexp st e2) ->
  gamma_par (abstract_eval_aexp ast (APlus e1 e2)) (eval_aexp st (APlus e1 e2)).
Proof.
  intros. simpl. apply gamma_distr_plus; assumption.
Qed.

Lemma abstract_aexp_mult_sound : forall ast st e1 e2,
  gamma_par (abstract_eval_aexp ast e1) (eval_aexp st e1) ->
  gamma_par (abstract_eval_aexp ast e2) (eval_aexp st e2) ->
  gamma_par (abstract_eval_aexp ast (AMult e1 e2)) (eval_aexp st (AMult e1 e2)).
Proof. intros. simpl. apply gamma_distr_mult; assumption.
Qed.

Lemma abstract_aexp_var_sound : forall ast st x,
  sound_state ast st ->
  gamma_par (abstract_eval_aexp ast (AVar x)) (eval_aexp st (AVar x)).
Proof. intros. simpl. auto. Qed.

Theorem abstract_aexp_eval_sound : forall ast st e,
  sound_state ast st ->
  (gamma_par (abstract_eval_aexp ast e)) (eval_aexp st e).
Proof.
  induction e; intros.
  - (* ANum *) simpl. apply gamma_extract_n_n.
  - (* AVar *) apply abstract_aexp_var_sound. apply H.

  - (* APlus *) apply abstract_aexp_plus_sound; auto.
  - (* AMult *) apply abstract_aexp_mult_sound; auto.
Qed.

Lemma abstract_ceval_ass_sound : forall ast st y a,
  sound_state ast st ->
  sound_state (ceval_abstract ast (y ::= a)) (ceval st (y ::= a)).
Proof.
  intros. simpl. unfold t_update, sound_state. intros.
  destruct (beq_string y x). 
  - apply abstract_aexp_eval_sound. apply H.
  - unfold sound_state in H. apply H.
Qed.

Theorem abstract_ceval_sound : forall ast st c,
  sound_state ast st ->
  sound_state (ceval_abstract ast c) (ceval st c).
Proof.
  unfold sound_state. intros ast st c. revert ast st.
  induction c.
  - (* SKIP *) auto.
  - (* CSeq *) simpl. intros.
    apply IHc2. clear IHc2. intros. apply IHc1. apply H.
  - intros. apply abstract_ceval_ass_sound. unfold sound_state. apply H.
Qed.

(* Add a statements SKIP, sequencing, if statements, assignment *)

(* TODO abstract store *)
(* TODO abstract bool *)
