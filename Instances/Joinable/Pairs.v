Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Pairs.

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

