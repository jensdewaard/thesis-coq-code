(* results *)

Require Import Coq.Classes.RelationClasses.

Require Import Joinable.
Require Import Preorder.

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
