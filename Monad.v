Definition State {S : Type} (A : Type) := S -> (A * S)%type.

Definition return_state {A S : Type} (x : A) : State A :=
  fun (st : S) => (x, st).

Definition bind_state {S A B : Type} (m : @State S A) (f : A -> @State S B) 
    : State B :=
  fun st => let (x, st') := (m st) in f x st'.

Definition get {S : Type} : State S := fun st => (st, st).

Definition put {S : Type} (st' : S) : @State S unit := fun st => (tt, st').
 

