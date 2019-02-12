Require Import Maps.
Require Import Parity.

Definition store := total_map nat.
Definition abstract_store := total_map parity.

Definition sound_store (ast : abstract_store) (st : store) : Prop := 
  forall x, gamma_par (ast x) (st x).

Definition abstract_store_top : abstract_store :=
  fun _ => par_top.
Definition abstract_store_bottom : abstract_store :=
  fun _ => par_bottom.
Definition abstract_store_join
    (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => parity_join (ast1 x) (ast2 x).

Lemma t_update_sound : forall ast st x p n,
  sound_store ast st ->
  sound_par p n ->
  sound_store (t_update ast x p) (t_update st x n).
Proof. 
  intros. unfold sound_store.  intros. unfold t_update. 
  destruct (beq_string x x0). 
  - unfold sound_par in H0. assumption.
  - unfold sound_store in H. apply H.
Qed.
