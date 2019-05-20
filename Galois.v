Require Import AbstractBool.
Require Import AbstractStore.
Require Import Monad.
Require Import Parity.
Require Import Preorder.
Require Import Result.
Require Import State.

Typeclasses eauto := 10.

Class Galois (A B : Type) `{PreorderedSet B} : Type :=
{
  gamma : B -> A -> Prop;
  gamma_monotone : monotone gamma;

}.
Arguments Build_Galois A B {_ _ _}.
Arguments gamma {_ _ _ _}.

Instance galois_parity_nat : Galois nat parity :=
{
  gamma := gamma_par;
  gamma_monotone := gamma_par_monotone;
}.

Instance galois_boolean : Galois bool abstr_bool :=
{
  gamma := gamma_bool;
  gamma_monotone := gamma_bool_monotone;
}.

Lemma widen {A B : Type} `{Galois B A}:
  forall (f f' : A) (b : B),
  preorder f f' -> gamma f b -> gamma f' b.
Proof.
  intros. apply preorder_props with (P:=(gamma f)).
  - apply gamma_monotone. assumption.
  - assumption.
Qed.

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

Section galois_options.
Context {B A} `{Galois B A}.

Definition gamma_option :
  option A -> option B -> Prop :=
  fun oa => fun ob => match oa, ob with
               | None, None => True
               | None, Some b => True
               | Some a, Some b => gamma a b
               | Some a, None => False
               end.

Lemma gamma_option_monotone  : 
  monotone gamma_option.
Proof.
  unfold monotone. intros a a' Hpre. simpl in *. constructor. 
  intros x Hgamma.
  inversion Hpre; subst.
  - assumption.
  - destruct x; constructor.
  - destruct x.
    + simpl. eapply widen. apply H1. apply Hgamma.
    + inversion Hgamma.
Qed.

Global Instance galois_option : 
  Galois (option B) (option A) := 
{
  gamma := gamma_option;
  gamma_monotone := gamma_option_monotone;  
}.
End galois_options.

Section galois_store.

Definition gamma_store : abstract_store -> store -> Prop :=
  fun st' => fun st => forall x, gamma (st' x) (st x).

Definition gamma_store_monotone : monotone gamma_store.
Proof. unfold monotone.
  intros ast ast'. simpl. constructor. intros st. unfold gamma_store in *. 
  intros Hgamma x. destruct H. eapply widen. apply H. apply Hgamma.
Qed.

Global Instance galois_store : Galois store abstract_store :=
{
  gamma := gamma_store;
  gamma_monotone := gamma_store_monotone;
}.

End galois_store.

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

Section galois_result.
Context {A A': Type} `{Galois A' A}.

Definition gamma_result : result A abstract_store -> result A' store -> Prop :=
  fun r1 => fun r2 => match r1, r2 with
                      | returnR _ _ x, returnR _ _ y => gamma x y
                      | crashed _ _ , _ => True
                      | exception _ _ st, exception _ _ st' => gamma st st'
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
    eapply widen. apply H1. auto.
Qed.

Global Instance galois_result :
  Galois (result A' store) (result A abstract_store) :=
{
  gamma := gamma_result;
  gamma_monotone := gamma_result_monotone;
}.

End galois_result.

Section galois_state.
Context {A A'} 
  `{Galois A A'}.

Global Instance galois_state :
  Galois (State A) (AbstractState A').
Proof.
  intros. unfold State, AbstractState. 
  assert (Galois (A*store) (A'*abstract_store)).
  { apply galois_pairs. }
  assert (Galois (option (A*store)) (option (A'*abstract_store))).
  { apply galois_option. }
  apply GFun. 
Defined.
End galois_state.

Section galois_unit.
Definition gamma_unit : 
  unit -> unit -> Prop :=  
  fun tt tt => True.

Lemma gamma_unit_monotone : monotone gamma_unit.
Proof.
  unfold monotone.
  intros. simpl. constructor. reflexivity.
Qed.

Global Instance galois_unit : Galois unit unit := 
{
  gamma := gamma_unit;
  gamma_monotone := gamma_unit_monotone;
}. 
End galois_unit.
