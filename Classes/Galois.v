Require Export Base.
Require Import PreorderedSet.
Require Import Instances.Preorder.

Class Galois (A B : Type) 
`{PreorderedSet B} : Type :=
{
  gamma : B -> A -> Prop;
  gamma_monotone : monotone gamma;

}.
Arguments Build_Galois A B {_ _ _}.
Arguments gamma {_ _ _ _}.

Ltac gamma_destruct := repeat
  match goal with
  | x : gamma _  _ |- _ => inv x
  end.

Lemma widen {A B : Type} `{Galois B A}:
  forall (f f' : A) (b : B),
  preorder f f' -> gamma f b -> gamma f' b.
Proof.
  intros.
  pose proof gamma_monotone.
  unfold monotone in H3. apply H3 in H1.
  simpl in H1. 
  unfold preordered_set_le in H1.
  auto.
Qed.

Ltac apply_widen :=
  match goal with
  | H : preorder ?a ?b, I : gamma ?a ?c |- gamma ?b ?c =>
      eapply widen; apply H + apply I
  end.
