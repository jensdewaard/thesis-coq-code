Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Unit.

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

