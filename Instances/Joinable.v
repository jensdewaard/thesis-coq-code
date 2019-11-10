Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Types.Result.
Require Import Types.Stores.
Require Import Instances.Monad.

Definition abstract_store_join
  (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => VTop.

Lemma abstract_store_join_comm : forall ast1 ast2,
  abstract_store_join ast1 ast2 = abstract_store_join ast2 ast1.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. reflexivity. 
Qed.

Lemma abstract_store_join_assoc : forall ast1 ast2 ast3,
  abstract_store_join ast1 (abstract_store_join ast2 ast3) =
  abstract_store_join (abstract_store_join ast1 ast2) ast3.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. reflexivity.
Qed.

Lemma abstract_store_join_upperbound_left :
    forall s s', preorder s (abstract_store_join s s').
Proof.
  simpl. unfold abstract_store_join. constructor.
  intro x. constructor.
Qed.

Lemma abstract_store_join_upperbound_right : 
  forall s s', preorder s' (abstract_store_join s s').
Proof.
  simpl. unfold abstract_store_join. constructor.
  intro x. constructor.
Qed.

Global Instance abstract_store_joinable : Joinable abstract_store := {
  join_op := abstract_store_join;
  join_upper_bound_left := abstract_store_join_upperbound_left;
  join_upper_bound_right := abstract_store_join_upperbound_right;
}.


Definition unit_join : unit -> unit -> unit :=
    fun _ _ => tt.

Lemma unit_join_upperbound_left : forall (u u' : unit),
  preorder u (unit_join u u').
Proof.
  intros. destruct u, u'. unfold unit_join. apply preorder_refl.
Qed.

Lemma unit_join_upperbound_right : forall (u u' : unit),
  preorder u' (unit_join u u').
Proof.
  intros. destruct u, u'. unfold unit_join. apply preorder_refl.
Qed.

Global Instance unit_joinable : Joinable unit :=
{
  join_op := unit_join;
  join_upper_bound_left := unit_join_upperbound_left;
  join_upper_bound_right := unit_join_upperbound_right
}.


Section result_joinable.
Context {A S : Type} `{Joinable A, Joinable S}.

Definition join_result (r1 r2 : abstract_result A S) : abstract_result A S :=
  match r1, r2 with
  | crashedA , _ | _, crashedA => crashedA 
  | exceptionA s1, exceptionA s2 => exceptionA (join_op s1 s2)
  | returnRA a1 s1, returnRA a2 s2 => returnRA (join_op a1 a2) (join_op s1 s2)
  | exceptionA s1, returnRA a2 s2 => exceptionOrReturn a2 (join_op s1 s2)
  | returnRA a1 s1, exceptionA s2 => exceptionOrReturn a1 (join_op s1 s2)
  | exceptionOrReturn a1 s1, exceptionOrReturn a2 s2 =>
      exceptionOrReturn (join_op a1 a2) (join_op s1 s2)
  | _ , _ => crashedA 
  end.

Lemma join_result_upperbound_left :
  forall r1 r2, preorder r1 (join_result r1 r2).
Proof. 
  intros r1 r2. simpl. destruct r1.
  - destruct r2; simpl; constructor. simpl. 
    apply join_upper_bound_left. apply join_upper_bound_left.
    apply join_upper_bound_left. apply preorder_refl.
  - simpl. constructor.
  - simpl. destruct r2; simpl; try constructor.
    apply join_upper_bound_left.
    apply join_upper_bound_left.
  - simpl. destruct r2; simpl; try constructor.
    apply join_upper_bound_left.
    apply join_upper_bound_left.
Qed.

Lemma join_result_upperbound_right :
  forall r1 r2, preorder r2 (join_result r1 r2).
Proof. 
  intros r1 r2. simpl. destruct r1.
  - destruct r2; simpl; constructor. simpl. 
    apply join_upper_bound_right.
    apply join_upper_bound_right.
    apply join_upper_bound_right.
  - simpl. constructor.
  - simpl. destruct r2; simpl; constructor.
    apply join_upper_bound_right.
    apply preorder_refl.
    apply join_upper_bound_right.
  - simpl. destruct r2; simpl; try constructor.
    apply join_upper_bound_right.
    apply join_upper_bound_right.
Qed.

Global Instance result_joinable : Joinable (abstract_result A S) := {
  join_op := join_result;
  join_upper_bound_left := join_result_upperbound_left;
  join_upper_bound_right := join_result_upperbound_right;
}.

End result_joinable.

Section state_joinable.
  Context {S A} `{Joinable S, Joinable A}.

  Definition state_join (st st' : State S A) : State S A :=
    fun x => ((join_op (fst (st x)) (fst (st' x)), 
              (join_op (snd (st x)) (snd (st' x))))).
  
  Lemma state_join_upper_bound_left :
    forall st st', preorder st (state_join st st').
  Proof. 
    intros. constructor. intros. unfold state_join.
    destruct (st x), (st' x). constructor;
    apply join_upper_bound_left. 
  Qed.

  Lemma state_join_upper_bound_right :
    forall st st', preorder st' (state_join st st').
  Proof.
    intros. constructor. intros. unfold state_join.
    destruct (st x), (st' x). constructor;
    apply join_upper_bound_right.
  Qed.

Global Instance state_joinable : Joinable (State S A) := {
  join_op := state_join;
  join_upper_bound_left := state_join_upper_bound_left;
  join_upper_bound_right := state_join_upper_bound_right;
}.
End state_joinable.

Section abstract_maybe_joinable.
Context {A : Type} `{Joinable A}.

Definition join_maybe_abstract
  (st1 st2 : AbstractMaybe A) : AbstractMaybe A :=
  match st1 with
  | NoneA => NoneA
  | JustA x => match st2 with
                 | NoneA  => NoneA
                 | JustA y => JustA (join_op x y)
                 | JustOrNoneA y => JustOrNoneA (join_op x y)
                 end
  | JustOrNoneA x => match st2 with
                       | NoneA => NoneA
                       | JustA y | JustOrNoneA y => 
                           JustOrNoneA (join_op x y)
                       end
  end.

Lemma join_maybe_abstract_upperbound_left : forall st st',
  preorder st (join_maybe_abstract st st').
Proof.
  intros. destruct st, st'; constructor; apply join_upper_bound_left.
Qed.

Lemma join_maybe_abstract_upperbound_right : forall st st',
  preorder st' (join_maybe_abstract st st').
Proof.
  intros. destruct st, st'; constructor; apply join_upper_bound_right.
Qed.

Global Instance abstract_maybe_joinable : Joinable (AbstractMaybe A) := 
{
  join_op := join_maybe_abstract;
  join_upper_bound_left := join_maybe_abstract_upperbound_left;
  join_upper_bound_right := join_maybe_abstract_upperbound_right;
}.

End abstract_maybe_joinable.


