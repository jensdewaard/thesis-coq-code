Require Import Utf8.
Require Import AbstractStore.


Definition State (S : Type) (A : Type) := S -> option (A * S)%type.

Definition return_state (S A : Type) (x : A) : State S A :=
  fun (st : S) => Some (x, st).

Definition bind_state (S A B : Type) (m : State S A) (f : A -> State S B) 
    : State S B :=
  fun st => match m st with
            | Some (x, st') => f x st'
            | None => None
            end.

Definition get {S : Type} : State S S := fun st => Some (st, st).

Definition put {S : Type} (st' : S) : State S unit := 
  fun st => Some (tt, st').

Definition fail {S A : Type} : State S A :=
  fun st => None.

 
Class Monad (M : Type -> Type) : Type :=
{
  returnM : forall A, A -> M A;
  bind : forall A B, M A  -> (A -> M B) -> M B;
}.
Arguments Build_Monad {_ _ _}.
Arguments returnM {_ _ _}.
Arguments bind {_ _ _ _}.

Instance state_monad {S : Type} : Monad (State S) := {
  returnM := (return_state S);
  bind := (bind_state S);
}.

Notation "x '<<' y ; z" := (bind y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bind x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).
