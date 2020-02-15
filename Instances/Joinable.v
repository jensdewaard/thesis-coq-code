Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Instances.Monad.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Types.Stores.

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
  join_assoc := abstract_store_join_assoc;
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

Lemma unit_join_assoc : ∀ x y z,
  unit_join x (unit_join y z) = unit_join (unit_join x y) z.
Proof.
  reflexivity.
Qed.

Global Instance unit_joinable : Joinable unit :=
{
  join_op := unit_join;
  join_upper_bound_left := unit_join_upperbound_left;
  join_upper_bound_right := unit_join_upperbound_right;
  join_assoc := unit_join_assoc;
}.

Section state_joinable.
  Context {S A} `{S_joinable : Joinable S, A_joinable : Joinable A}.

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

  Lemma state_join_assoc : ∀ x y z,
    state_join x (state_join y z) = state_join (state_join x y) z.
  Proof.
    intros. unfold state_join. extensionality a.
    destruct (x a), (y a), (z a); simpl. repeat rewrite join_assoc. 
    reflexivity.
  Qed.

  Global Instance state_joinable : Joinable (State S A) := {
    join_op := state_join;
    join_upper_bound_left := state_join_upper_bound_left;
    join_upper_bound_right := state_join_upper_bound_right;
    join_assoc := state_join_assoc;
  }.
End state_joinable.

Section maybe_joinable.
  Context {A : Type} `{A_joinable : Joinable A}.

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

  Definition join_maybe_assoc : ∀ x y z, 
    join_maybe x (join_maybe y z) = join_maybe (join_maybe x y) z.
  Proof.
    intros. destruct x, y, z; try reflexivity.
    simpl. rewrite join_assoc. reflexivity.
  Qed.

  Global Instance maybe_joinable : Joinable (Maybe A) :=
  {
    join_op := join_maybe;
    join_upper_bound_left := join_maybe_left;
    join_upper_bound_right := join_maybe_right;
    join_assoc := join_maybe_assoc;
  }.
End maybe_joinable.

Section abstract_maybe_joinable.
Context {A : Type} `{A_joinable : Joinable A}.

Definition join_maybe_abstract
  (st1 st2 : AbstractMaybe A) : AbstractMaybe A :=
  match st1, st2 with
  | NoneA, NoneA => NoneA
  | JustA x, JustA y => JustA (join_op x y)
  | JustA x, NoneA | NoneA, JustA x =>  JustOrNoneA x
  | NoneA, JustOrNoneA x | JustOrNoneA x, NoneA => JustOrNoneA x
  | JustA x, JustOrNoneA y | JustOrNoneA x, JustA y => 
      JustOrNoneA (join_op x y)
  | JustOrNoneA x, JustOrNoneA y => JustOrNoneA (join_op x y)
  end.
Hint Unfold join_maybe_abstract : soundness.

Lemma join_maybe_abstract_upperbound_left : forall st st',
  preorder st (join_maybe_abstract st st').
Proof. simple_solve. Qed.

Lemma join_maybe_abstract_upperbound_right : forall st st',
  preorder st' (join_maybe_abstract st st').
Proof. simple_solve. Qed.

Lemma join_maybe_abstract_assoc : ∀ x y z : AbstractMaybe A,
  join_maybe_abstract x (join_maybe_abstract y z) =
  join_maybe_abstract (join_maybe_abstract x y) z.
Proof.
  intros. destruct x, y, z; simpl; try reflexivity.
  all: repeat rewrite join_assoc; reflexivity.
Qed.

Global Instance abstract_maybe_joinable : Joinable (AbstractMaybe A) := 
{
  join_op := join_maybe_abstract;
  join_upper_bound_left := join_maybe_abstract_upperbound_left;
  join_upper_bound_right := join_maybe_abstract_upperbound_right;
  join_assoc := join_maybe_abstract_assoc;
}.

End abstract_maybe_joinable.

Section joinable_pairs.
  Context {A B} `{A_joinable : Joinable A, B_joinable : Joinable B}.

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

  Lemma join_pair_assoc : ∀ x y z, 
    join_pair x (join_pair y z) = join_pair (join_pair x y) z.
  Proof.
    intros. destruct x as [x1 x2], y as [y1 y2], z as [z1 z2]. 
    unfold join_pair; simpl. repeat rewrite join_assoc.
    reflexivity.
  Qed.

  Global Instance joinable_pairs : Joinable (A*B) :=
  {
    join_op := join_pair;
    join_upper_bound_left := join_pair_left;
    join_upper_bound_right := join_pair_right;
    join_assoc := join_pair_assoc;
  }.
End joinable_pairs.

Section joinable_maybeT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T}, 
    Joinable (M T)}.

  Global Instance maybeT_joinable {A} `{A_joinable : Joinable A} :
    Joinable (MaybeT M A) :=
  {
    join_op := join_op;
    join_upper_bound_left := join_upper_bound_left;
    join_upper_bound_right := join_upper_bound_right;
    join_assoc := join_assoc;
  }.
End joinable_maybeT.

Section joinable_maybeAT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T}, 
    Joinable (M T)}.

  Global Instance maybeAT_joinable {A} `{A_joinable : Joinable A} : 
    Joinable (MaybeAT M A) :=
  {
    join_op := join_op;
    join_upper_bound_left := join_upper_bound_left;
    join_upper_bound_right := join_upper_bound_right;
    join_assoc := join_assoc;
  }.
End joinable_maybeAT.

Section joinable_stateT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {S A : Type} `{S_joinable : Joinable S, A_joinable : Joinable A}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T},
    Joinable (M T)}.

  Definition join_stateT (st st' : StateT S M A) : StateT S M A :=
    λ x, join_op (st x) (st' x).

  Lemma join_stateT_upper_bound_left : ∀ t t' : StateT S M A,
    preorder t (join_stateT t t').
  Proof.
    intros. unfold join_stateT. constructor. intros. 
    apply join_upper_bound_left.
  Qed.

  Lemma join_stateT_upper_bound_right : ∀ t t' : StateT S M A, 
    preorder t' (join_stateT t t').
  Proof.
    intros. unfold join_stateT. constructor. intros.
    apply join_upper_bound_right.
  Qed.

  Lemma join_stateT_assoc : ∀ x y z,
    join_stateT x (join_stateT y z) = join_stateT (join_stateT x y) z.
  Proof.
    intros. unfold join_stateT. extensionality s.
    rewrite join_assoc. reflexivity.
  Qed.

  Global Instance stateT_joinable : Joinable (StateT S M A) :=
  {
    join_op := join_stateT;
    join_upper_bound_left := join_stateT_upper_bound_left;
    join_upper_bound_right := join_stateT_upper_bound_right;
    join_assoc := join_stateT_assoc;
  }.
End joinable_stateT.
