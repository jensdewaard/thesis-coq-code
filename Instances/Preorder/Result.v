Require Import Coq.Classes.RelationClasses.

Require Import Classes.PreorderedSet.
Require Import Types.Result.

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
