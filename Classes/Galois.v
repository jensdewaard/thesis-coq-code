Require Export Base.
Require Import Classes.Joinable.
Require Import Instances.Preorder.
Require Import PreorderedSet.

Class Galois (A A' : Type) `{A'_preorder: PreorderedSet A'} : Type :=
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

Lemma gamma_preorder {A A'} `{A_galois : Galois A A'}: forall (a' a2' : A') (a : A), 
    preorder a' a2' -> gamma a' a -> gamma a2' a.
Proof.
  intros a a' b Hpre Hgamma.
  pose proof gamma_monotone as Hmono.
  unfold monotone in Hmono. apply Hmono in Hpre.
  destruct Hpre. auto with soundness.
Qed.

Lemma gamma_join_left {A A'} `{A'_joinable : Joinable A'} 
  `{A_galois : @Galois A A' T_preorder} : ∀ (a : A) (a'1 a'2 : A'),
  gamma a'1 a → gamma (join_op a'1 a'2) a.
Proof. 
  intros. apply (gamma_preorder a'1). 
  apply join_upper_bound_left. assumption.
Qed.

Lemma gamma_join_right {A A'} `{A'_joinable : Joinable A'} 
  `{A_galois : @Galois A A' T_preorder} : ∀ (a : A) (a'1 a'2 : A'),
  gamma a'2 a → gamma (join_op a'1 a'2) a.
Proof. 
  intros. apply (gamma_preorder a'2). 
  apply join_upper_bound_right. assumption.
Qed.

Ltac apply_widen :=
  match goal with
  | H : preorder ?a ?b, I : gamma ?a ?c |- gamma ?b ?c =>
      eapply gamma_preorder; apply H + apply I
  end.
