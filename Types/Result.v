(* results *)

Require Import Coq.Classes.RelationClasses.

Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.

Inductive result (A S : Type) : Type :=
  | returnR : A -> S -> result A S
  | crashed : result A S
  | exception : S -> result A S.
  
Inductive abstract_result (A S : Type) :=
  | returnRA : A -> S -> abstract_result A S
  | crashedA : abstract_result A S
  | exceptionA : S -> abstract_result A S
  | exceptionOrReturn : A -> S -> abstract_result A S.

Section result_preorder.
Context {A S: Type} `{PreorderedSet A, PreorderedSet S}.

Inductive result_le : abstract_result A S -> abstract_result A S -> Prop :=
  | result_le_crashed : forall r, result_le r (crashedA A S)
  | result_le_exception : forall s1 s2, 
      preorder s1 s2 -> result_le (exceptionA A S s1) (exceptionA A S s2)
  | result_le_return : forall a1 a2 s1 s2, 
      preorder a1 a2 -> 
      preorder s1 s2 ->
      result_le (returnRA A S a1 s1) (returnRA A S a2 s2)
  | result_le_exception_or : forall a st1 st2, 
      preorder st1 st2 -> 
      result_le (exceptionA A S st1) (exceptionOrReturn A S a st2)
  | result_le_return_or : forall a1 a2 s1 s2,
      preorder s1 s2 ->
      preorder a1 a2 ->
      result_le (returnRA A S a1 s1) (exceptionOrReturn A S a2 s2)
  | result_le_or_or : forall a1 a2 s1 s2,
      preorder a1 a2 ->
      preorder s1 s2 ->
      result_le (exceptionOrReturn A S a1 s1) (exceptionOrReturn A S a2 s2).


Lemma result_le_refl :
  Reflexive result_le.
Proof.
  unfold Reflexive. destruct x; try constructor; try apply preorder_refl.
Qed.

Lemma result_le_trans :
  Transitive result_le.
Proof.
  unfold Transitive.
  intros x y z H1 H2.
  inversion H1; inversion H2; subst; 
  try constructor; try inversion H2; subst; auto; eapply preorder_trans;
  try apply H3; try apply H4; auto.
Qed.

Global Instance result_preorder : PreorderedSet (abstract_result A S) := {
  preorder := result_le;
  preorder_refl := result_le_refl;
  preorder_trans := result_le_trans;
}.
End result_preorder.

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
