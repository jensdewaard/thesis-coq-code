Require Export Base.
Require Import Classes.Joinable.
Require Import Instances.Preorder.
Require Import PreorderedSet.

Class Galois (A A' : Type) `{A'_preorder: PreorderedSet A'} : Type :=
{
  γ : A' -> ℘ A;
  gamma_monotone : monotone γ;
}.
Arguments γ : simpl never.
Hint Extern 10 (γ _ _) => constructor : soundness.

Ltac gamma_destruct := repeat
  match goal with
  | x : γ _  _ |- _ => inv x
  end.

Lemma gamma_preorder {A A'} `{A_galois : Galois A A'}: forall (a' a2' : A') (a : A), 
    preorder a' a2' -> γ a' a -> γ a2' a.
Proof.
  intros a a' b Hpre Hgamma.
  pose proof gamma_monotone as Hmono.
  unfold monotone in Hmono. apply Hmono in Hpre.
  destruct Hpre. auto with soundness.
Qed.

Lemma gamma_join_left {A A'} `{A'_joinable : Joinable A'} 
  `{A_galois : @Galois A A' T_preorder} : ∀ (a : A) (a'1 a'2 : A'),
  γ a'1 a → γ (join_op a'1 a'2) a.
Proof. 
  intros. apply (gamma_preorder a'1). 
  apply join_upper_bound_left. assumption.
Qed.

Lemma gamma_join_right {A A'} `{A'_joinable : Joinable A'} 
  `{A_galois : @Galois A A' T_preorder} : ∀ (a : A) (a'1 a'2 : A'),
  γ a'2 a → γ (join_op a'1 a'2) a.
Proof. 
  intros. apply (gamma_preorder a'2). 
  apply join_upper_bound_right. assumption.
Qed.

Ltac apply_widen :=
  match goal with
  | H : preorder ?a ?b, I : γ ?a ?c |- γ ?b ?c =>
      eapply gamma_preorder; apply H + apply I
  end.
