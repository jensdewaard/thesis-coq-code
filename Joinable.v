Require Import AbstractStore.
Require Import Parity.
Require Import Preorder.

Class Joinable (T : Type) `{PreorderedSet T} : Type :=
{
  join_op : T -> T -> T;
  join_upper_bound: forall t t', preorder t (join_op t t');
  join_comm : forall t t', join_op t t' = join_op t' t;
}.

Lemma parity_join_upperbound :
  forall p p', preorder p (parity_join p p').
Proof.
  intros. simpl. unfold parity_join. destruct p, p'; constructor.
Qed.

Instance parity_joinable : Joinable parity := {
  join_op := parity_join;
  join_upper_bound := parity_join_upperbound;
  join_comm := parity_join_comm;
}.

Section option_joinable.
Context {A} `{Joinable A}.
Definition option_join (o1 o2 : option A) : option A :=
  match o1, o2 with
  | Some x, Some y => Some (join_op x y)
  | _, _ => None
  end.

Lemma option_join_upperbound : forall o o', preorder o (option_join o o').
Proof.
  intros. simpl. destruct o, o'; constructor.
  apply join_upper_bound.
Qed.

Lemma option_join_comm : forall o o', option_join o o' = option_join o' o.
Proof.
  intros. destruct o, o'; try reflexivity.
  unfold option_join. rewrite join_comm. reflexivity.
Qed.

Global Instance option_joinable : Joinable (option A) := 
{
  join_op := option_join;
  join_upper_bound := option_join_upperbound;
  join_comm := option_join_comm;
}.

End option_joinable.

Section pair_joinable.
Context {A B} `{Joinable A, Joinable B}.

Definition pair_join (p1 p2 : A*B) : A*B :=
  ((join_op (fst p1) (fst p2)), (join_op (snd p1) (snd p2))).

Lemma pair_join_upperbound : forall p p', 
  preorder p (pair_join p p').
Proof.
  intros. simpl. destruct p, p'. constructor;
  simpl; apply join_upper_bound.
Qed.

Lemma pair_join_comm : forall p p',
  pair_join p p' = pair_join p' p.
Proof.
  unfold pair_join. intros. rewrite -> join_comm. 
  replace (join_op (snd p )(snd p')) with (join_op (snd p') (snd p)).
  reflexivity. apply join_comm.
Qed.

Global Instance pair_joinable : Joinable (prod A B) :=
{
  join_op := pair_join;
  join_upper_bound := pair_join_upperbound;
  join_comm := pair_join_comm;
}.
End pair_joinable.

Instance abstract_store_joinable : Joinable abstract_store := {
  join_op := abstract_store_join;
  join_comm := abstract_store_join_comm;
}.
Proof.
simpl. unfold abstract_store_join. constructor.  
intro x. apply parity_join_upperbound.
Defined.

Section unit_joinable.

Definition unit_join : unit -> unit -> unit :=
  fun _ _ => tt.

Lemma unit_join_upperbound : forall (u u' : unit),
  preorder u (unit_join u u').
Proof.
  intros. destruct u, u'. unfold unit_join. apply preorder_refl.
Qed.

Global Instance unit_joinable : Joinable unit :=
{
  join_op := unit_join;
  join_upper_bound := unit_join_upperbound;
}.
Proof.
  destruct t, t'. reflexivity.
Defined.
End unit_joinable.

