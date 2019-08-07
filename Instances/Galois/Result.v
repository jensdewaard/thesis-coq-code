Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Instances.Galois.AbstractStore.
Require Import Types.Result.
Require Import Types.AbstractStore.

Section galois_result.
Context {A A': Type} `{Galois A' A}.

Definition gamma_result : abstract_result A abstract_store -> 
                          result A' store -> Prop :=
  fun r1 => fun r2 => match r1, r2 with
                      | returnRA _ _ a s, returnR _ _  b t => 
                          gamma a b /\ gamma s t
                      | crashedA _ _ , _ => True
                      | exceptionA _ _ st, exception _ _ st' => gamma st st'
                      | exceptionOrReturn _ _ x st, exception _ _ st' =>
                          gamma st st'
                      | exceptionOrReturn _ _ x st, returnR _ _ x' st' =>
                          gamma st st' /\ gamma x x'
                      | _, _ => False
                      end.

Lemma gamma_result_monotone :
  monotone gamma_result.
Proof.
  unfold monotone. intros a a' Hpred. simpl in *. constructor. 
  intros x Hgamma.
  inversion Hpred; subst.
  - reflexivity.
  - destruct x; try inversion Hgamma.
    eapply widen. apply H1. apply Hgamma.
  - destruct x; try inversion Hgamma.
    split; eapply widen. apply H1. auto. apply H2. auto.
  - destruct x; try inversion Hgamma.
    eapply widen. apply H1. apply Hgamma.
  - destruct x; try inversion Hgamma.
    split; eapply widen. apply H1. apply H4. apply H2. apply H3.
  - destruct x; try inversion Hgamma.
    + split. eapply widen. apply H2. apply H3.
      eapply widen. apply H1. apply H4.
    + eapply widen. apply H2. apply Hgamma.
Qed.

Global Instance galois_result :
  Galois (result A' store) (abstract_result A abstract_store) :=
{
  gamma := gamma_result;
  gamma_monotone := gamma_result_monotone;
}.

End galois_result.
