Require Export Base.

Class PreorderedSet (X : Type) : Type :=
{
  preorder : X -> X -> Prop;
  preorder_refl: forall x, preorder x x;
  preorder_trans: forall x y z, preorder x y -> preorder y z -> preorder x z;
}.
Hint Resolve preorder_refl preorder_trans : soundness.
Hint Extern 10 (preorder _ _) => constructor : soundness.

Definition monotone {A B} `{A_pre : PreorderedSet A, B_pre : PreorderedSet B} :
  (A -> B) -> Prop :=
  fun f => forall (a a': A), preorder a a' -> preorder (f a) (f a').
  
Hint Unfold monotone : soundness.

Ltac pre_trans :=
  match goal with
  | H : preorder ?a ?b, K : preorder ?b ?c  |- preorder ?a ?c =>
      eapply preorder_trans; [apply H|assumption]
  end.
