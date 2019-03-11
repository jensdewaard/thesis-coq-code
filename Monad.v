Require Import AbstractStore.


Definition State (A : Type) := store -> (A * store)%type.

Definition return_state {A : Type} (x : A) : State A :=
  fun (st : store) => (x, st).

Definition bind_state {A B : Type} (m : State A) (f : A -> State B) : State B :=
  fun st => let (x, st') := (m st) in f x st'.

Definition get : State store := fun st => (st, st).

Definition put (st' : store) : State unit := fun st => (tt, st).
 

