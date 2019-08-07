(* State and AbstractStates *)

Require Import AbstractStore.
Require Import Joinable.
Require Import Language.Statements.
Require Import Classes.PreorderedSet.
Require Import Preorder.
Require Import Result.
Require Import Monad.

Definition State (A : Type) := 
  store -> result A store.

Definition return_state (A : Type) (x : A) : State A :=
  fun st => returnR A store x st.

Definition bind_state (A B : Type) (m : State A) (f : A -> State B) 
    : State B :=
  fun st => match m st with
            | returnR _ _ x st' => f x st'
            | crashed _ _ => crashed _ _
            | exception _ _ st' => exception _ _ st'
            end.

Definition get : State store := fun st => returnR store store st st.

Definition put (st' : store) : State unit := 
  fun st => returnR unit store tt st'.
  
Definition fail {A : Type} : State A :=
  fun st => exception A store st.

Definition AbstractState (A : Type) :=
  abstract_store -> abstract_result A abstract_store.

Definition return_state_abstract (A : Type) (x : A) : AbstractState A :=
  fun st => returnRA A abstract_store x st.

Definition bind_state_abstract (A B : Type)
  (m : AbstractState A) (f : A -> AbstractState B) : AbstractState B :=
  fun st => match m st with
            | returnRA _ _ x st' => f x st'
            | crashedA _ _ => crashedA _ _
            | exceptionA _ _ st' => exceptionA _ _ st' 
            | exceptionOrReturn _ _ x st' => match (f x st') with
                                             | returnRA _ _ x' st'' => 
                                                  exceptionOrReturn _ _ x' st''
                                             | crashedA _ _ => crashedA _ _
                                             | exceptionA _ _ st'' =>
                                                  exceptionA _ _ (join_op st' st'')
                                             | exceptionOrReturn _ _ x' st'' =>
                                                  exceptionOrReturn _ _ x' (join_op st' st'')
                                             end
            end.

Definition get_abstract : AbstractState abstract_store := 
  fun st => returnRA abstract_store abstract_store st st.

Definition put_abstract (st' : abstract_store) : AbstractState unit :=
  fun st => returnRA unit abstract_store tt st'.

Definition fail_abstract {A : Type} : AbstractState A :=
  fun st => exceptionA A abstract_store st.

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
  bindM := (bind_state);
}.

Instance abstract_state_monad : Monad (AbstractState) := {
  returnM := return_state_abstract;
  bindM := bind_state_abstract;
}.

