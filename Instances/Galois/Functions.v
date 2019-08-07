Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Functions.


Section galois_functions.
Context {A A' B B' : Type} 
  `{Galois B A, Galois B' A'}.

Definition gamma_fun (f' : A-> A') (f : B -> B') : 
Prop :=
  forall (a : A) (b : B), gamma a b -> gamma (f' a) (f b).

Lemma gamma_fun_monotone :
  monotone gamma_fun.
Proof.
  constructor.
  intros x Hgamma. unfold gamma_fun in *. 
  intros a0 b Hgamma2.
  apply widen with (f:= a a0). destruct H3; apply H3.
  apply Hgamma. apply Hgamma2.
Qed.

Global Instance GFun : 
  Galois (B -> B') (A->A') :=
{
  gamma := gamma_fun;
  gamma_monotone := gamma_fun_monotone;
}.

End galois_functions.
