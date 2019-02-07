Require Import Maps.
Require Import Parity.

Definition state := total_map nat.
Definition abstract_state := total_map parity.

Definition sound_state (ast : abstract_state) (st : state) : Prop := 
  forall x, gamma_par (ast x) (st x).

Lemma t_update_sound : forall ast st x p n,
  sound_state ast st ->
  sound_par p n ->
  sound_state (t_update ast x p) (t_update st x n).
Proof. 
  intros. unfold sound_state.  intros. unfold t_update. 
  destruct (beq_string x x0). 
  - unfold sound_par in H0. assumption.
  - unfold sound_state in H. apply H.
Qed.
