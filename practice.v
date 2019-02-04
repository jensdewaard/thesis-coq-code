Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

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
  gamma (abstract_eval_aexp ast e1) (eval_aexp st e1) ->
  gamma (abstract_eval_aexp ast e2) (eval_aexp st e2) ->
  gamma (abstract_eval_aexp ast (APlus e1 e2)) (eval_aexp st (APlus e1 e2)).
Proof.
  intros. simpl. apply gamma_distr_plus; assumption.
Qed.

Lemma abstract_aexp_mult_sound : forall ast st e1 e2,
  gamma (abstract_eval_aexp ast e1) (eval_aexp st e1) ->
  gamma (abstract_eval_aexp ast e2) (eval_aexp st e2) ->
  gamma (abstract_eval_aexp ast (AMult e1 e2)) (eval_aexp st (AMult e1 e2)).
Proof. intros. simpl. apply gamma_distr_mult; assumption.
Qed.

Theorem abstract_aexp_eval_sound : forall ast st e,
  (forall x, gamma (ast x) (st x)) ->
  (gamma (abstract_eval_aexp ast e)) (eval_aexp st e).
Proof.
  induction e; intros.
  - (* ANum *)
    simpl. apply gamma_extract_n_n.
  - (* AVar *)
    simpl. apply H.
  - (* APlus *)
    apply abstract_aexp_plus_sound; auto.
  - (* AMult *)
    apply abstract_aexp_mult_sound; auto.
Qed.

Lemma abstract_ceval_seq_sound : forall ast c1 c2 x st,
  gamma ((ceval_abstract ast c1) x) ((ceval st c1) x) ->
  gamma (ceval_abstract ast (c1;; c2) x) (ceval st (c1;; c2) x).
Proof.
   intros. generalize dependent c1. induction c2; intros.
   - auto.
   - replace (ceval_abstract ast (c1;; c2_1;; c2_2))
     with (ceval_abstract ast ((c1;; c2_1);; c2_2)).
     apply IHc2_2. apply IHc2_1. assumption.
     reflexivity.
Qed.

Theorem abstract_ceval_sound : forall ast st c x,
  (forall x, gamma (ast x) (st x)) ->
  (gamma ((ceval_abstract ast c) x)) ((ceval st c) x).
Proof.
  intros. induction c.
  - (* SKIP *)
    intros. simpl. apply H.
  - (* CSeq *)
    apply abstract_ceval_seq_sound. assumption.
Qed.
    


(* proof the equivalance of the galois connection diagram *)
(* Peval o gamma \subset gamma o abstract_eval *)
(* etc... *)

(* Add a statements SKIP, sequencing, if statements, assignment *)

(* TODO abstract store *)
(* TODO abstract bool *)
