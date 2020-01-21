Require Export Base.
Require Import Classes.Joinable.
Require Import Instances.Preorder.
Require Import PreorderedSet.

Class Galois (A A' : Type) `{PreorderedSet A'} : Type :=
{
  gamma : A' -> A -> Prop;
  gamma_monotone : monotone gamma;
}.
Arguments gamma : simpl never.
Hint Extern 10 (gamma _ _) => constructor : soundness.

Ltac gamma_destruct := repeat
  match goal with
  | x : gamma _  _ |- _ => inv x
  end.

Lemma gamma_preorder {A B} `{Galois B A}: forall (a a' : A) (b : B), 
    preorder a a' -> gamma a b -> gamma a' b.
Proof.
  intros a a' b Hpre Hgamma.
  pose proof gamma_monotone as Hmono.
  unfold monotone in Hmono. apply Hmono in Hpre.
  destruct Hpre. auto with soundness.
Qed.

Lemma gamma_join_left {A A'} `{Joinable A'} `{_ : @Galois A A' H} : ∀ (a : A) (a'1 a'2 : A'),
  gamma a'1 a → gamma (join_op a'1 a'2) a.
Proof. 
  intros. apply (gamma_preorder a'1). 
  apply join_upper_bound_left. assumption.
Qed.

Lemma gamma_join_right {A A'} `{Joinable A'} `{_ : @Galois A A' H} : ∀ (a : A) (a'1 a'2 : A'),
  gamma a'2 a → gamma (join_op a'1 a'2) a.
Proof. 
  intros. apply (gamma_preorder a'2). apply join_upper_bound_right.
  assumption.
Qed.

Ltac apply_widen :=
  match goal with
  | H : preorder ?a ?b, I : gamma ?a ?c |- gamma ?b ?c =>
      eapply gamma_preorder; apply H + apply I
  end.
