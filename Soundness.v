Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractBool.
Require Import AbstractStore.
Require Import AbstractInterpreter.
Require Import Aux.
Require Import ConcreteInterpreter.
Require Import Parity.
Require Import Preorder.
Require Import Maps.
Require Import Language.

Open Scope com_scope.

Lemma abstract_aexp_plus_sound : forall e1 e2,
  sound_aexp e1 ->
  sound_aexp e2 ->
  sound_aexp (APlus e1 e2).
Proof. 
  unfold sound_aexp. intros. simpl. apply parity_plus_sound. 
  apply H. assumption.
  apply H0. assumption.
Qed.

Lemma abstract_aexp_mult_sound : forall e1 e2,
  sound_aexp e1 ->
  sound_aexp e2 ->
  sound_aexp (AMult e1 e2).
Proof.
  unfold sound_aexp. intros. apply parity_mult_sound. apply H. assumption.
  apply H0. assumption. Qed.

Lemma abstract_aexp_var_sound : forall x,
  sound_aexp (AVar x).
Proof. intros. unfold sound_aexp. intros. simpl. unfold sound_store in H.
  apply H. Qed.

Theorem abstract_aexp_eval_sound : forall e,
  sound_aexp e.
Proof. 
  induction e; intros.
  - (* ANum *) unfold sound_aexp. intros. simpl. apply gamma_extract_n_n.
  - (* AVar *) apply abstract_aexp_var_sound. 
  - (* APlus *) apply abstract_aexp_plus_sound; auto.
  - (* AMult *) apply abstract_aexp_mult_sound; auto.
Qed.

Lemma abstract_beval_eq_sound : forall a1 a2,
  sound_bexp (BEq a1 a2).
Proof.
  unfold sound_bexp. intros. 
  unfold sound_ab. apply parity_eq_sound.
  apply abstract_aexp_eval_sound. assumption. apply abstract_aexp_eval_sound.
  assumption.
Qed.

Theorem abstract_beval_sound : forall e,
  sound_bexp e.
Proof. 
  unfold sound_bexp. intros. induction e.
  - reflexivity. 
  - simpl. tauto. 
  - apply abstract_beval_eq_sound. assumption. 
  - reflexivity.
  - simpl. apply neg_ab_sound. assumption.
  - simpl. apply and_ab_sound. assumption. assumption.
Qed.

Lemma abstract_ceval_ass_sound : forall y a,
  sound_com (y ::= a).
Proof.
  unfold sound_com. 
  intros. simpl. unfold t_update, sound_store. intros.
  destruct (beq_string y x). 
  - apply abstract_aexp_eval_sound. apply H.
  - unfold sound_store in H. apply H.
Qed.

Lemma abstract_ceval_seq_sound : forall c1 c2,
  sound_com c1 ->
  sound_com c2 ->
  sound_com (c1 ;; c2).
Proof. 
  unfold sound_com. intros. apply H0. apply H. assumption.
Qed.

Lemma abstract_ceval_if_sound : forall b c1 c2,
  sound_com c1 ->
  sound_com c2 ->
  sound_com (CIf b c1 c2).
Proof. 
  unfold sound_com. intros. simpl. 
  pose proof abstract_beval_sound. unfold sound_bexp in H2. 
  assert (sound_ab (beval_abstract ast b) (eval_bexp st b)).
  { apply H2. assumption. }
  destruct (eval_bexp st b), (beval_abstract ast b);
    unfold sound_ab, gamma_bool, not in H3; try inversion H3.
  - apply H; assumption.
  - exfalso. apply H3. reflexivity.
  - simpl. apply abstract_store_join_sound_left. auto.
  - simpl. auto. 
  - simpl. apply abstract_store_join_sound_right. auto.
Qed.

Theorem abstract_ceval_sound : forall c,
  sound_com c.
Proof. 
  intros c. induction c; intros.
  - (* SKIP *) unfold sound_com. simpl. intros. assumption.
  - (* CSeq *) apply abstract_ceval_seq_sound; assumption.
  - apply abstract_ceval_ass_sound.
  - apply abstract_ceval_if_sound; assumption.
Qed.

Record IsGalois {A B} (g : B -> A -> Prop)  
                      (e : A->B)
                      (j : B->B->B) 
                      (o : B->B->Prop) :=
{
}.


Class Galois (A B : Type) `{PreorderedSet A} `{PreorderedSet B} : Type :=
{
  gamma : B -> A -> Prop;
  gamma_monotone : forall b b', preorder b b' -> preorder (gamma b) (gamma b');  
}.
Arguments Build_Galois A B {_ _ _ _}.
Arguments gamma {_ _ _ _ _}.
Print gamma.

Instance galois_self {A :Type} `{PreorderedSet A} : Galois A A :=
{
  gamma := fun _ _ => True;
}.
- intros. simpl. constructor.
Defined.
(* 
Discuss with Sven

- Add an extract function to the galois definition?
- Definition of soundness

- forall n, gamma (extract n) n.
  *)

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


Definition sound {A B A' B' : Type} 
  `{Galois A B} `{Galois A' B'}
  (f : A->A) (f' : B->B) :=
  forall b a, gamma b a -> gamma (f' b) (f a).

Definition sound2 {A B : Type} `{Galois A B} (f :A -> A -> A) (f' : B-> B -> B) :=
  forall a1 a2 b1 b2 , gamma b1 a1 -> gamma b2 a2 -> gamma (f' b1 b2) (f a1 a2). 

Theorem sound_parity_plus :
  sound2 plus parity_plus.
Proof.
  unfold sound2; intros. apply parity_plus_sound; assumption.
Qed.

