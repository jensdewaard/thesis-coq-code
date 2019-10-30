(* State and AbstractStates *)

Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Instances.Joinable.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Classes.Monad.
Require Import Types.Result.
Require Import Types.Stores.
Require Import Types.Maps.
Require Import Instances.Monad.

Definition State (A : Type)         := Maybe (state (total_map cvalue) A).
Definition AbstractState (A : Type) := AbstractMaybe (state (total_map avalue) A).

(*
Definition return_state {A : Type} (x : A) : State A :=
  fun st => returnR x st.
Arguments return_state [_] _.

Definition bind_state {A B : Type} (m : State A) (f : A -> State B) 
    : State B :=
  fun st => match m st with
            | returnR x st' => f x st'
            | crashed => crashed 
            | exception st' => exception st'
            end.
Arguments bind_state [_ _] _ _.

Definition get : State store := fun st => returnR st st.

Definition put (st' : store) : State unit := 
  fun st => returnR tt st'.
  

Definition AbstractState (A : Type) :=
  abstract_store -> abstract_result A abstract_store.

Definition return_state_abstract {A : Type} (x : A) : AbstractState A :=
  fun st => returnRA x st.
Arguments return_state_abstract [_] _.

Definition bind_state_abstract {A B : Type}
  (m : AbstractState A) (f : A -> AbstractState B) : AbstractState B :=
  fun st => match m st with
            | returnRA x st' => f x st'
            | crashedA => crashedA 
            | exceptionA st' => exceptionA st' 
            | exceptionOrReturn x st' => match (f x st') with 
                                         | returnRA x' st'' => 
                                             exceptionOrReturn x' 
                                                              (join_op st' st'')
                                         | crashedA => crashedA 
                                         | exceptionA st'' => 
                                             exceptionA (join_op st' st'')
                                         | exceptionOrReturn x' st'' => 
                                             exceptionOrReturn x' 
                                                (join_op st' st'')
                                         end
            end.
Arguments bind_state_abstract [_ _] _ _.
*)

Section abstract_state_joinable.
Context {A : Type} `{Joinable A}.


Definition join_state_abstract
  (st1 st2 : AbstractState A) : AbstractState A :=
  match st1 with
  | NoneA _ => NoneA _
  | JustA _ x => match st2 with
                 | NoneA _ => NoneA _
                 | JustA _ y => JustA _ (join_op x y)
                 | JustOrNoneA _ y => JustOrNoneA _ (join_op x y)
                 end
  | JustOrNoneA _ x => match st2 with
                       | NoneA _ => NoneA _
                       | JustA _ y | JustOrNoneA _ y => 
                           JustOrNoneA _ (join_op x y)
                       end
  end.

Lemma join_state_abstract_upperbound_left : forall st st',
  preorder st (join_state_abstract st st').
Proof.
  intros. destruct st, st'; constructor; apply join_upper_bound_left.
Qed.

Lemma join_state_abstract_upperbound_right : forall st st',
  preorder st' (join_state_abstract st st').
Proof.
  intros. destruct st, st'; constructor; apply join_upper_bound_right.
Qed.

Global Instance abstract_state_joinable : Joinable (AbstractState A) := 
{
  join_op := join_state_abstract;
  join_upper_bound_left := join_state_abstract_upperbound_left;
  join_upper_bound_right := join_state_abstract_upperbound_right;
}.

End abstract_state_joinable.


