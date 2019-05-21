(* results *)

Require Import Coq.Classes.RelationClasses.

Require Import Joinable.
Require Import Classes.PreorderedSet.
Require Import Preorder.

Inductive result (A S : Type) : Type :=
  | returnR : A -> S -> result A S
  | crashed : result  A S
  | exception : S -> result A S.

Section result_preorder.
Context {A S: Type} `{PreorderedSet A, PreorderedSet S}.

Inductive result_le : result A S -> result A S -> Prop :=
  | result_le_crashed : forall r, result_le r (crashed A S)
  | result_le_exception : forall s1 s2, 
      preorder s1 s2 -> result_le (exception A S s1) (exception A S s2)
  | result_le_return : forall a1 a2 s1 s2, 
      preorder a1 a2 -> 
      preorder s1 s2 ->
      result_le (returnR A S a1 s1) (returnR A S a2 s2).

Lemma result_le_refl :
  Reflexive result_le.
Proof.
  unfold Reflexive. destruct x; constructor;
  apply preorder_refl.
Qed.

Lemma result_le_trans :
  Transitive result_le.
Proof.
  unfold Transitive.
  intros x y z H1 H2.
  inversion H1; inversion H2; subst; 
  try constructor; try inversion H2; subst. 
  injection H7 as H9; subst. eapply preorder_trans.
  apply H3. apply H6.
  eapply preorder_trans.  apply H3. apply H11.
  eapply preorder_trans. apply H4. apply H13.
Qed.

Global Instance result_preorder : PreorderedSet (result A S) := {
  preorder := result_le;
  preorder_refl := result_le_refl;
  preorder_trans := result_le_trans;
}.
End result_preorder.

Section result_joinable.
Context {A S : Type} `{Joinable A, Joinable S}.

Definition join_result (r1 r2 : result A S) : result A S :=
  match r1, r2 with
  | crashed _ _, _ | _, crashed _ _ => crashed A S
  | exception _ _ s1, exception _ _ s2 => exception A S (join_op s1 s2)
  | returnR _ _ a1 s1, returnR _ _ a2 s2 => returnR A S (join_op a1 a2) (join_op s1 s2)
  | _ , _ => crashed A S
  end.

Lemma join_result_upperbound_left :
  forall r1 r2, preorder r1 (join_result r1 r2).
Proof. 
  intros r1 r2. simpl. destruct r1.
  - destruct r2; simpl; constructor. simpl. 
    apply join_upper_bound_left. apply join_upper_bound_left.
  - simpl. constructor.
  - simpl. destruct r2; simpl; try constructor.
    apply join_upper_bound_left.
Qed.

Lemma join_result_upperbound_right :
  forall r1 r2, preorder r2 (join_result r1 r2).
Proof. 
  intros r1 r2. simpl. destruct r1.
  - destruct r2; simpl; constructor. simpl. 
    apply join_upper_bound_right.
    apply join_upper_bound_right.
  - simpl. constructor.
  - simpl. destruct r2; simpl; constructor.
    apply join_upper_bound_right.
Qed.

Global Instance result_joinable : Joinable (result A S) := {
  join_op := join_result;
  join_upper_bound_left := join_result_upperbound_left;
  join_upper_bound_right := join_result_upperbound_right;
}.

End result_joinable.
