Require Import Utf8.

Definition State {S : Type} (A : Type) := S -> (A * S)%type.

Definition return_state {S A : Type} (x : A) : State A :=
  fun (st : S) => (x, st).

Definition bind_state {S A B : Type} (m : @State S A) (f : A -> @State S B) 
    : State B :=
  fun st => let (x, st') := (m st) in f x st'.

Definition get {S : Type} : State S := fun st => (st, st).

Definition put {S : Type} (st' : S) : @State S unit := fun st => (tt, st').
 
Class Monad (M : Type -> Type) : Type :=
{
  returnM : forall A, A -> M A;
  bind : forall A B, M A  -> (A -> M B) -> M B;
}.

Instance state_monad {S : Type} : Monad (@State S) := 
{
  returnM := (@return_state S);
  bind := (@bind_state S);
}.


Notation "x '<<' y ; z" := (bind_state y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bind_state x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).
