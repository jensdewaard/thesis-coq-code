Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Pairs.

Section galois_pairs.
Context {A B C D} `{Galois B A} `{Galois D C}.

Definition gamma_pairs :
  prod A C-> prod B D -> Prop := 
  fun (p1 : A*C) (p2 : B*D) => 
  gamma (fst p1) (fst p2) /\ gamma (snd p1) (snd p2).

Lemma gamma_pairs_monotone :
  monotone gamma_pairs.
Proof.
  unfold monotone. intros [a c] [a' c'].
  intro Hpre. simpl. constructor. intros [b d]. unfold gamma_pairs; simpl.
  intros [Hab Hac]. inversion Hpre; subst. split.
  - eapply widen. apply H6. apply Hab.
  - eapply widen. apply H8. apply Hac. 
Qed.

Global Instance galois_pairs :
  Galois (B*D) (A*C) :=
{
  gamma := gamma_pairs;
  gamma_monotone := gamma_pairs_monotone;
}.
End galois_pairs.

