Require Import Utf8.
Require Import Coq.Classes.RelationClasses.

Require Import AbstractStore.
Require Import Joinable.
Require Import Preorder.
Require Import FunctionalExtensionality.

Inductive result (A : Type) : Type :=
  | returnR : A -> result A
  | crashed : result A
  | failed : result A.

Definition State (S : Type) (A : Type) := 
  S -> ((result A) * S)%type.

Definition return_state (S A : Type) (x : A) : State S A :=
  fun (st : S) => (returnR A x, st).

Definition bind_state (S A B : Type) (m : State S A) (f : A -> State S B) 
    : State S B :=
  fun st => match m st with
            | (returnR _ x, st') => f x st'
            | (crashed _, st') => (crashed B, st')
            | (failed _, st') => (failed B, st')
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

Definition get {S : Type} : State S S := fun st => (returnR S st, st).

Definition put {S : Type} (st' : S) : State S unit := 
  fun st => (returnR unit tt, st').
  
Definition fail {S A : Type} : State S A :=
  fun st => (failed A, st).

Section result_preorder.
Context {A : Type} `{PreorderedSet A}.

Inductive result_le : result A -> result A -> Prop :=
  | result_le_crashed : forall r, result_le r (crashed A)
  | result_le_failed : result_le (failed A) (failed A)
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
  | failed _, failed _ => failed A
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

Section state_joinable.
Context {S A : Type} `{Joinable S} `{Joinable A}.

Definition join_state
  (st1 st2 : State S A) : State S A :=
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
