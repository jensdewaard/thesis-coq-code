Require Import Classes.Applicative.
Require Import Classes.Functor.
Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Instances.Monad.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Types.Stores.
Require Import Types.State.

Definition abstract_store_join
  (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => VTop.

Lemma abstract_store_join_comm : forall ast1 ast2,
  abstract_store_join ast1 ast2 = abstract_store_join ast2 ast1.
Proof. simple_solve. Qed.

Lemma abstract_store_join_assoc : forall ast1 ast2 ast3,
  abstract_store_join ast1 (abstract_store_join ast2 ast3) =
  abstract_store_join (abstract_store_join ast1 ast2) ast3.
Proof. simple_solve. Qed.

Lemma abstract_store_join_upperbound_left :
    forall s s', preorder s (abstract_store_join s s').
Proof. 
  eauto with soundness.
Qed.

Lemma abstract_store_join_upperbound_right : 
  forall s s', preorder s' (abstract_store_join s s').
Proof. eauto with soundness. Qed.

Global Instance abstract_store_joinable : Joinable abstract_store := {
  join_op := abstract_store_join;
  join_upper_bound_left := abstract_store_join_upperbound_left;
  join_upper_bound_right := abstract_store_join_upperbound_right;
}.

Definition unit_join : unit -> unit -> unit :=
    fun _ _ => tt.
Hint Unfold unit_join : soundness.

Lemma unit_join_upperbound_left : forall (u u' : unit),
  preorder u (unit_join u u').
Proof. simple_solve. Qed.

Lemma unit_join_upperbound_right : forall (u u' : unit),
  preorder u' (unit_join u u').
Proof. simple_solve. Qed.

Global Instance unit_joinable : Joinable unit :=
{
  join_op := unit_join;
  join_upper_bound_left := unit_join_upperbound_left;
  join_upper_bound_right := unit_join_upperbound_right
}.

Section state_joinable.
  Context {S A} `{Joinable S, Joinable A}.

  Definition state_join (st st' : State S A) : State S A :=
    fun x => ((join_op (fst (st x)) (fst (st' x)), 
              (join_op (snd (st x)) (snd (st' x))))).
  Hint Unfold state_join : soundness.
  
  Lemma state_join_upper_bound_left :
    forall st st', preorder st (state_join st st').
  Proof. 
    intros st st'. unfold state_join.
    simpl. constructor. intro x. destruct (st x). 
    constructor; eauto with soundness.
  Qed.

  Lemma state_join_upper_bound_right :
    forall st st', preorder st' (state_join st st').
  Proof. 
    intros st st'. unfold state_join. constructor.
    intro x. destruct (st' x). constructor; eauto with soundness.
  Qed.

Global Instance state_joinable : Joinable (State S A) := {
  join_op := state_join;
  join_upper_bound_left := state_join_upper_bound_left;
  join_upper_bound_right := state_join_upper_bound_right;
}.
End state_joinable.

Section maybe_joinable.
  Context {A : Type} `{Joinable A}.

  Definition join_maybe (m n : Maybe A) : Maybe A :=
    match m, n with
    | Just x, Just y => Just (join_op x y)
    | _, _ => None
    end.

  Definition join_maybe_left : ∀ m n, preorder m (join_maybe m n).
  Proof.
    destruct m, n; simpl; auto with soundness. 
  Qed.

  Definition join_maybe_right : ∀ m n, preorder n (join_maybe m n).
  Proof. destruct m, n; simpl; auto with soundness. Qed.

  Global Instance maybe_joinable : Joinable (Maybe A) :=
  {
    join_op := join_maybe;
    join_upper_bound_left := join_maybe_left;
    join_upper_bound_right := join_maybe_right;
  }.
End maybe_joinable.

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
Hint Unfold join_maybe_abstract : soundness.

Lemma join_maybe_abstract_upperbound_left : forall st st',
  preorder st (join_maybe_abstract st st').
Proof. simple_solve. Qed.

Lemma join_maybe_abstract_upperbound_right : forall st st',
  preorder st' (join_maybe_abstract st st').
Proof. simple_solve. Qed.

Global Instance abstract_maybe_joinable : Joinable (AbstractMaybe A) := 
{
  join_op := join_maybe_abstract;
  join_upper_bound_left := join_maybe_abstract_upperbound_left;
  join_upper_bound_right := join_maybe_abstract_upperbound_right;
}.

End abstract_maybe_joinable.

Section joinable_pairs.
  Context {A B} `{Joinable A, Joinable B}.

  Definition join_pair (p q : (A*B)%type) : (A*B)%type :=
    (join_op (fst p) (fst q), join_op (snd p) (snd q)).

  Lemma join_pair_left : ∀ p q, preorder p (join_pair p q).
  Proof.
    destruct p, q. eauto with soundness.
  Qed.

  Lemma join_pair_right : ∀ p q, preorder q (join_pair p q).
  Proof.
    destruct p, q. eauto with soundness.
  Qed.

  Global Instance joinable_pairs : Joinable (A*B) :=
  {
    join_op := join_pair;
    join_upper_bound_left := join_pair_left;
    join_upper_bound_right := join_pair_right;
  }.
End joinable_pairs.

Section joinable_maybeAT_state.
  Context {S A} `{Joinable A, Joinable S}.

  Global Instance maybeAT_state_joinable : Joinable (MaybeAT (State S) A) :=
  {
    join_op := state_join;
    join_upper_bound_left := state_join_upper_bound_left;
    join_upper_bound_right := state_join_upper_bound_right;
  }.
End joinable_maybeAT_state.

Section joinable_abstract_state.
  Context {A} `{Joinable A}.
  
  Definition join_abstract_state (st1 st2 : AbstractState A) : AbstractState A :=
    λ st, join_op (st1 st) (st2 st).
  Hint Unfold join_abstract_state : soundness.

  Lemma join_abstract_state_left : ∀ st st', 
    preorder st (join_abstract_state st st').
  Proof.
    eauto with soundness.
  Qed.

  Lemma join_abstract_store_right : ∀ st st',
    preorder st' (join_abstract_state st st').
  Proof. 
    eauto with soundness.
  Qed.
  
  Global Instance abstract_state_joinable : Joinable (AbstractState A) :=
  {
    join_op := join_abstract_state;
    join_upper_bound_left := join_abstract_state_left;
    join_upper_bound_right := join_abstract_store_right;
  }.
End joinable_abstract_state.
