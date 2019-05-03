Require Import AbstractStore.
Require Import Parity.
Require Import Preorder.

Class Joinable (T : Type) `{PreorderedSet T} : Type :=
{
  join_op : T -> T -> T;
  join_upper_bound_left: forall t t', preorder t (join_op t t');
  join_upper_bound_right: forall t t', preorder t' (join_op t t');
}.

Lemma parity_join_upperbound_left :
  forall p p', preorder p (parity_join p p').
Proof.
  intros. simpl. unfold parity_join. destruct p, p'; constructor.
Qed.

Lemma parity_join_upperbound_right :
  forall p p', preorder p' (parity_join p p').
Proof.
  intros. simpl. unfold parity_join. destruct p, p'; constructor.
Qed.

Instance parity_joinable : Joinable parity := {
  join_op := parity_join;
  join_upper_bound_left := parity_join_upperbound_left;
  join_upper_bound_right := parity_join_upperbound_right;
}.

Section option_joinable.
Context {A} `{Joinable A}.
Definition option_join (o1 o2 : option A) : option A :=
  match o1, o2 with
  | Some x, Some y => Some (join_op x y)
  | _, _ => None
  end.

Lemma option_join_upperbound_left : forall o o', preorder o (option_join o o').
Proof.
  intros. simpl. destruct o, o'; constructor.
  apply join_upper_bound_left.
Qed.

Lemma option_join_upperbound_right : 
  forall o o', preorder o' (option_join o o').
Proof.
  intros. simpl. destruct o, o'; constructor.
  apply join_upper_bound_right.
Qed.

Global Instance option_joinable : Joinable (option A) := 
{
  join_op := option_join;
  join_upper_bound_left := option_join_upperbound_left;
  join_upper_bound_right := option_join_upperbound_right;
}.

End option_joinable.

Section pair_joinable.
Context {A B} `{Joinable A, Joinable B}.

Definition pair_join (p1 p2 : A*B) : A*B :=
  ((join_op (fst p1) (fst p2)), (join_op (snd p1) (snd p2))).

Lemma pair_join_upperbound_left : forall p p', 
  preorder p (pair_join p p').
Proof.
  intros. simpl. destruct p, p'. constructor;
  simpl; apply join_upper_bound_left.
Qed.

Lemma pair_join_upperbound_right : forall p p',
  preorder p' (pair_join p p').
Proof.
  intros. simpl. destruct p, p'. constructor;
  simpl; apply join_upper_bound_right.
Qed.


Global Instance pair_joinable : Joinable (prod A B) :=
{
  join_op := pair_join;
  join_upper_bound_left := pair_join_upperbound_left;
  join_upper_bound_right := pair_join_upperbound_right;
}.
End pair_joinable.

Section store_joinable.

Lemma abstract_store_join_upperbound_left :
  forall s s', preorder s (abstract_store_join s s').
Proof.
  simpl. unfold abstract_store_join. constructor.
  intro x. apply parity_join_upperbound_left.
Qed.

Lemma abstract_store_join_upperbound_right : 
  forall s s', preorder s' (abstract_store_join s s').
Proof.
  simpl. unfold abstract_store_join. constructor.
  intro x. apply parity_join_upperbound_right.
Qed.

Global Instance abstract_store_joinable : Joinable abstract_store := {
  join_op := abstract_store_join;
  join_upper_bound_left := abstract_store_join_upperbound_left;
  join_upper_bound_right := abstract_store_join_upperbound_right;
}.

End store_joinable.

Section unit_joinable.

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

End unit_joinable.

