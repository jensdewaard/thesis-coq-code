Require Import Utf8.
Require Import AbstractStore.
Require Import Joinable.
Require Import Preorder.
Require Import FunctionalExtensionality.

Definition State (S : Type) (A : Type) := S -> option (A * S)%type.

Definition return_state (S A : Type) (x : A) : State S A :=
  fun (st : S) => Some (x, st).

Definition bind_state (S A B : Type) (m : State S A) (f : A -> State S B) 
    : State S B :=
  fun st => match m st with
            | Some (x, st') => f x st'
            | None => None
            end.

(*
Inductive result
  | return
  | fail
  | crashd
in de monad state

fix semantiek van catch mbv bovenstaande
merge de evaluatie van bools en nats
abstract en concrete values/monads/state/etc
  *)

Definition get {S : Type} : State S S := fun st => Some (st, st).

Definition put {S : Type} (st' : S) : State S unit := 
  fun st => Some (tt, st').
  
Definition fail {S A : Type} : State S A :=
  fun st => None.

Section state_joinable.
Context {S A : Type} `{Joinable S} `{Joinable A}.

Definition join_state
  (st1 st2 : State S A) : State S A :=
  fun st => join_op (st1 st) (st2 st).
  
Lemma join_state_upperbound_left : forall st st',
  preorder st (join_state st st').
Proof.
  intros. simpl. constructor. intros. simpl. 
  unfold join_state. simpl. apply option_join_upperbound_left.
Qed.

Lemma join_state_upperbound_right : forall st st',
  preorder st' (join_state st st').
Proof.
  intros. simpl. constructor. intros. simpl.
  unfold join_state. simpl. apply option_join_upperbound_right.
Qed.

Global Instance state_joinable : Joinable (State S A) := {
  join_op := join_state;
  join_upper_bound_left := join_state_upperbound_left;
  join_upper_bound_right := join_state_upperbound_right;
}.
End state_joinable.

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

Section preordered_state.
Context {S A : Type} `{PreorderedSet S, PreorderedSet A}.

Lemma preorder_state : 
  PreorderedSet (State S A).
Proof. 
  intros. unfold State. assert (PreorderedSet (A*S)). 
  apply preorder_pairs. assert (PreorderedSet (option (A*S))).
  apply preorder_option.
  apply preordered_function_spaces. 
Qed.
End preordered_state.

Notation "x '<<' y ; z" := (bind y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bind x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).
