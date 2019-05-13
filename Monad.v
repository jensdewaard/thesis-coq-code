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
Require Import Utf8.
Require Import Coq.Classes.RelationClasses.

Require Import AbstractStore.
Require Import Joinable.
Require Import Preorder.
Require Import FunctionalExtensionality.

Inductive result (A : Type) : Type :=
  | returnR : A -> result A
  | crashed : result A
  | exception : result A.

Section result_preorder.
Context {A : Type} `{PreorderedSet A}.

Inductive result_le : result A -> result A -> Prop :=
  | result_le_crashed : forall r, result_le r (crashed A)
  | result_le_exception : result_le (exception A) (exception A)
  | result_le_return : forall a1 a2, 
      preorder a1 a2 -> result_le (returnR A a1) (returnR A a2).

Lemma result_le_refl :
  Reflexive result_le.
Proof.
  unfold Reflexive. destruct x; constructor.
  apply preorder_refl.
Qed.

Lemma result_le_trans :
  Transitive result_le.
Proof.
  unfold Transitive.
  intros x y z H1 H2.
  inversion H1; inversion H2; subst; 
  try constructor; try inversion H2; subst.
  injection H6 as H8; subst. eapply preorder_trans.
  apply H0. apply H5.
Qed.

Global Instance result_preorder : PreorderedSet (result A) := {
  preorder := result_le;
  preorder_refl := result_le_refl;
  preorder_trans := result_le_trans;
}.
End result_preorder.

Section result_joinable.
Context {A : Type} `{Joinable A}.

Definition join_result (r1 r2 : result A) : result A :=
  match r1, r2 with
  | crashed _, _ | _, crashed _ => crashed A
  | exception _, exception _ => exception A
  | returnR _ a1, returnR _ a2 => returnR A (join_op a1 a2)
  | _ , _ => crashed A
  end.

Lemma join_result_upperbound_left :
  forall r1 r2, preorder r1 (join_result r1 r2).
Proof. 
  intros r1 r2. simpl. destruct r1.
  - destruct r2; simpl; constructor. apply join_upper_bound_left.
  - simpl. constructor.
  - simpl. destruct r2; simpl; constructor.
Qed.

Lemma join_result_upperbound_right :
  forall r1 r2, preorder r2 (join_result r1 r2).
Proof. 
  intros r1 r2. simpl. destruct r1.
  - destruct r2; simpl; constructor.
    apply join_upper_bound_right.
  - simpl. constructor.
  - simpl. destruct r2; simpl; constructor.
Qed.

Global Instance result_joinable : Joinable (result A) := {
  join_op := join_result;
  join_upper_bound_left := join_result_upperbound_left;
  join_upper_bound_right := join_result_upperbound_right;
}.

End result_joinable.

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

Class Monad (M : Type -> Type) : Type :=
{
  returnM : forall A, A -> M A;
  bind : forall A B, M A  -> (A -> M B) -> M B;
}.
Arguments Build_Monad {_ _ _}.
Arguments returnM {_ _ _}.
Arguments bind {_ _ _ _}.

Instance state_monad : Monad (State) := {
  returnM := (return_state);
  bind := (bind_state);
}.

Instance abstract_state_monad : Monad (AbstractState) := {
  returnM := return_state_abstract;
  bind := bind_state_abstract;
}.

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

Notation "x '<<' y ; z" := (bind y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bind x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).
