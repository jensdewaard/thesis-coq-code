(* State and AbstractStates *)

Require Import AbstractStore.
Require Import Joinable.
Require Import Classes.PreorderedSet.
Require Import Preorder.
Require Import Result.
Require Import Monad.

Definition State (A : Type) := 
  store -> result A store.

Definition return_state (A : Type) (x : A) : State A :=
  fun st => returnR A store (x, st).

Definition bind_state (A B : Type) (m : State A) (f : A -> State B) 
    : State B :=
  fun st => match m st with
            | returnR _ _ (x, st') => f x st'
            | crashed _ _ => crashed _ _
            | exception _ _ st' => exception _ _ st'
            end.

Definition get : State store := fun st => returnR store store (st, st).

Definition put (st' : store) : State unit := 
  fun st => returnR unit store (tt, st').
  
Definition fail {A : Type} : State A :=
  fun st => exception A store st.

Definition AbstractState (A : Type) :=
  abstract_store -> result A abstract_store.

Definition return_state_abstract (A : Type) (x : A) : AbstractState A :=
  fun st => returnR A abstract_store (x, st).

Definition bind_state_abstract (A B : Type) 
  (m : AbstractState A) (f : A -> AbstractState B) : AbstractState B :=
  fun st => match m st with
            | returnR _ _ (x, st') => f x st'
            | crashed _ _ => crashed _ _
            | exception _ _ st' => exception _ _ st' 
            end.

Definition get_abstract : AbstractState abstract_store := 
  fun st => returnR abstract_store abstract_store (st, st).

Definition put_abstract (st' : abstract_store) : AbstractState unit :=
  fun st => returnR unit abstract_store (tt, st').

Definition fail_abstract {A : Type} : AbstractState A :=
  fun st => exception A abstract_store st.

Section abstract_state_joinable.
Context {A : Type} `{Joinable A}.

Definition join_state_abstract
  (st1 st2 : AbstractState A) : AbstractState A :=
  fun st => join_op (st1 st) (st2 st).

Lemma join_state_abstract_upperbound_left : forall st st',
  preorder st (join_state_abstract st st').
Proof.
  intros. simpl. constructor. intro x. simpl.
  unfold join_state_abstract. apply join_result_upperbound_left.
Qed.

Lemma join_state_abstract_upperbound_right : forall st st',
  preorder st' (join_state_abstract st st').
Proof.
  intros. simpl. constructor. intro x. simpl.
  unfold join_state_abstract. apply join_result_upperbound_right.
Qed.

Global Instance abstract_state_joinable : Joinable (AbstractState A) := 
{
  join_op := join_state_abstract;
  join_upper_bound_left := join_state_abstract_upperbound_left;
  join_upper_bound_right := join_state_abstract_upperbound_right;
}.

End abstract_state_joinable.

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

