Require Import Maps.
Require Import Parity.

Definition state := total_map nat.
Definition abstract_state := total_map parity.

Definition sound_state (ast : abstract_state) (st : state) : Prop := 
  forall x, gamma_par (ast x) (st x).
