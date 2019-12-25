Require Export Base.
Require Import PreorderedSet.
Require Import Instances.Preorder.

Implicit Type A B : Type.

Class Galois A B : Type :=
{
  galois_preorder :> PreorderedSet B;
  gamma : B -> A -> Prop;
  gamma_monotone : monotone gamma;

}.
Arguments gamma : simpl never.
Hint Extern 10 (gamma _ _) => constructor : soundness.

Ltac gamma_destruct := repeat
  match goal with
  | x : gamma _  _ |- _ => inv x
  end.

Lemma widen {A B} `{Galois B A}: forall (a a' : A) (b : B), 
    preorder a a' -> gamma a b -> gamma a' b.
Proof.
  intros a a' b Hpre Hgamma.
  pose proof gamma_monotone as Hmono.
  unfold monotone in Hmono. apply Hmono in Hpre.
  destruct Hpre. auto with soundness.
Qed.

Ltac apply_widen :=
  match goal with
  | H : preorder ?a ?b, I : gamma ?a ?c |- gamma ?b ?c =>
      eapply widen; apply H + apply I
  end.
