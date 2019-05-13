(* State and AbstractStates *)

Require Import AbstractStore.
Require Import Joinable.
Require Import Preorder.
Require Import Result.
Require Import Monad.

Definition State (A : Type) := 
  store -> ((result A) * store)%type.

Definition return_state (A : Type) (x : A) : State A :=
  fun st => (returnR A x, st).

Definition bind_state (A B : Type) (m : State A) (f : A -> State B) 
    : State B :=
  fun st => match m st with
            | (returnR _ x, st') => f x st'
            | (crashed _, st') => (crashed B, st')
            | (exception _, st') => (exception B, st')
            end.

Definition get : State store := fun st => (returnR store st, st).

Definition put (st' : store) : State unit := 
  fun st => (returnR unit tt, st').
  
Definition fail {A : Type} : State A :=
  fun st => (exception A, st).

Definition AbstractState (A : Type) :=
  abstract_store -> ((result A) * abstract_store)%type.

Definition return_state_abstract (A : Type) (x : A) : AbstractState A :=
  fun st => (returnR A x, st).

Definition bind_state_abstract (A B : Type) 
  (m : AbstractState A) (f : A -> AbstractState B) : AbstractState B :=
  fun st => match m st with
            | (returnR _ x, st') => f x st'
            | (crashed _  , st') => (crashed B, st')
            | (exception _   , st') => (exception B, st') 
            end.

Definition get_abstract : AbstractState abstract_store := 
  fun st => (returnR abstract_store st, st).

Definition put_abstract (st' : abstract_store) : AbstractState unit :=
  fun st => (returnR unit tt, st').

Definition fail_abstract {A : Type} : AbstractState A :=
  fun st => (exception A, st).

Section state_joinable.
Context {A : Type}  `{Joinable A}.

Definition join_state
  (st1 st2 : State A) : State A :=
  fun st => join_op (st1 st) (st2 st).
  
Lemma join_state_upperbound_left : forall st st',
  preorder st (join_state st st').
Proof.
  intros. simpl. constructor. intros. simpl. 
  unfold join_state. simpl. apply pair_join_upperbound_left.
Qed.

Lemma join_state_upperbound_right : forall st st',
  preorder st' (join_state st st').
Proof.
  intros. simpl. constructor. intros. simpl.
  unfold join_state. simpl. apply pair_join_upperbound_right.
Qed.

Global Instance state_joinable : Joinable (State A) := {
  join_op := join_state;
  join_upper_bound_left := join_state_upperbound_left;
  join_upper_bound_right := join_state_upperbound_right;
}.
End state_joinable.

Section abstract_state_joinable.
Context {A : Type} `{Joinable A}.

Definition join_state_abstract
  (st1 st2 : AbstractState A) : AbstractState A :=
  fun st => join_op (st1 st) (st2 st).

Lemma join_state_abstract_upperbound_left : forall st st',
  preorder st (join_state_abstract st st').
Proof.
  intros. simpl. constructor. intro x. simpl.
  unfold join_state_abstract. apply pair_join_upperbound_left.
Qed.

Lemma join_state_abstract_upperbound_right : forall st st',
  preorder st' (join_state_abstract st st').
Proof.
  intros. simpl. constructor. intro x. simpl.
  unfold join_state_abstract. apply pair_join_upperbound_right.
Qed.

Global Instance abstract_state_joinable : Joinable (AbstractState A) := 
{
  join_op := join_state_abstract;
  join_upper_bound_left := join_state_abstract_upperbound_left;
  join_upper_bound_right := join_state_abstract_upperbound_right;
}.

End abstract_state_joinable.

Section preordered_state.
Context {A : Type} `{PreorderedSet A}.

Lemma preorder_state : 
  PreorderedSet (State A).
Proof. 
  intros. unfold State. assert (PreorderedSet (A*store)). 
  apply preorder_pairs. assert (PreorderedSet (option (A*store))).
  apply preorder_option.
  apply preordered_function_spaces. 
Qed.
End preordered_state.

Section preordered_abstract_state.
Context {A : Type} `{PreorderedSet A}.

Lemma preorder_abstract_state : PreorderedSet (AbstractState A).
Proof.
  intros. 
  apply preordered_function_spaces.
Qed.

End preordered_abstract_state.

Instance state_monad : Monad (State) := {
  returnM := (return_state);
  bind := (bind_state);
}.

Instance abstract_state_monad : Monad (AbstractState) := {
  returnM := return_state_abstract;
  bind := bind_state_abstract;
}.

