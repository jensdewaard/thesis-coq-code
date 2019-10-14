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

Lemma widen {A B : Type} `{Galois B A}:
  forall (f f' : A) (b : B),
  preorder f f' -> gamma f b -> gamma f' b.
Proof.
  intros.
  pose proof gamma_monotone.
  unfold monotone in H3. apply H3 in H1.
  simpl in H1. 
  destruct H1. apply H1. apply H2.
Qed.

