Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Result.
Require Import Types.Result.

Section result_joinable.
Context {A S : Type} `{Joinable A, Joinable S}.

Definition join_result (r1 r2 : abstract_result A S) : abstract_result A S :=
  match r1, r2 with
  | crashedA _ _, _ | _, crashedA _ _ => crashedA A S
  | exceptionA _ _ s1, exceptionA _ _ s2 => exceptionA A S (join_op s1 s2)
  | returnRA _ _ a1 s1, returnRA _ _ a2 s2 => returnRA A S (join_op a1 a2) (join_op s1 s2)
  | exceptionA _ _ s1, returnRA _ _ a2 s2 => exceptionOrReturn A S a2 (join_op s1 s2)
  | returnRA _ _ a1 s1, exceptionA _ _ s2 => exceptionOrReturn A S a1 (join_op s1 s2)
  | exceptionOrReturn _ _ a1 s1, exceptionOrReturn _ _ a2 s2 =>
      exceptionOrReturn A S (join_op a1 a2) (join_op s1 s2)
  | _ , _ => crashedA A S
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
