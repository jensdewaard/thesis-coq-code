Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractBool.
Require Import AbstractStore.
Require Import AbstractInterpreter.
Require Import ConcreteInterpreter.
Require Import Galois.
Require Import Language.
Require Import Maps.
Require Import Monad.
Require Import Parity.
Require Import Preorder.

Definition sound {A B A' B' : Type} 
  `{Galois B A} `{Galois B' A'}
  (f : B->B') (f' : A->A') :=
  forall b a, gamma a b -> gamma (f' a) (f b).
  
Lemma bind_state_sound {S S' A A' B B'} 
`{Galois S S', Galois A A', Galois B B'}
: 
forall next next' f f',
sound f f' ->
sound next next' ->
sound (bind_state S A B f next) (bind_state S' A' B' f' next').
Proof.
  intros. simpl. unfold gamma_fun. intros. simpl. unfold sound. intros b a H10.
  simpl. unfold bind_state. unfold sound in H8. 
  assert (gamma (f' a) (f b)); auto. 
  destruct (f' a) eqn:Hf'a; destruct (f b) eqn:Hfb.
  - destruct p, p0. apply H9. simpl in H11. apply H11. apply H11.
  - inversion H11.
  - simpl.  destruct p. destruct (next a0 s); reflexivity.
  - reflexivity. 
Qed.

Tactic Notation "bind" := apply bind_state_sound;[auto| |auto].

Tactic Notation "pairs" := unfold gamma_pairs; simpl; split.

Lemma sound_parity_plus :
  sound plus parity_plus.
Proof. intros ? ? ? ? ? ?.
  unfold sound. simpl. unfold gamma_fun; intros. simpl. 
  destruct a, a0; simpl in *; try tauto;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.

Lemma sound_parity_mult :
  sound mult parity_mult.
Proof. 
  unfold sound. simpl. unfold gamma_fun. intros. simpl.
  destruct a, a0; simpl in *; try tauto; 
  auto using even_mult_l, even_mult_r, odd_mult.
Qed.

Lemma sound_parity_eq :
  sound Nat.eqb parity_eq.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct a, a0; simpl in *; try tauto; unfold not; intros.
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd. 
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd.
Qed.

Lemma sound_ab_and :
  sound andb and_ab.
Proof. 
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.

Lemma sound_ab_or :
  sound orb or_ab.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.

Lemma sound_ab_neg :
  sound negb neg_ab.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, a; simpl in *; tauto.
Qed.

Theorem eval_aexp_sound :
  forall a, sound (eval_aexp a) (abstract_eval_aexp a).
Proof.
  intros.
  unfold sound. simpl.
  induction a.
  - (* ANum *) simpl. unfold gamma_pairs; simpl. split.
    + apply gamma_par_extract_n_n.
    + apply H.
  - (* AVar *) simpl. unfold gamma_pairs; simpl. split.
    + simpl in H. unfold gamma_store in H. apply H.
    + apply H.
  - (* APlus *) simpl in *. intros st ast H. apply bind_state_sound.
    + unfold sound. intros st' ast' Hgamma. simpl in Hgamma. 
      apply IHa1. apply Hgamma.
    + unfold sound. intros n p Hgamma. simpl. unfold gamma_fun. 
      intros ast' st'. intros Hstore. simpl. apply bind_state_sound.
      * unfold sound. intros st'' ast''. intros Hgamma'. apply IHa2.
        assumption.
      * unfold sound. intros n' p' Hgamma'. simpl. unfold gamma_fun.
        intros ast'' st'' Hgamma''. simpl. unfold gamma_pairs; simpl; split.
        { apply sound_parity_plus; assumption. }
        { apply Hgamma''. }
      * apply Hstore.
    + apply H.
  - (* AMult *) intros st ast Hstore. simpl. 
    apply bind_state_sound; unfold sound.
    + intros st' ast' Hstore'. simpl. apply IHa1; assumption.
    + intros n p Hpar. simpl. unfold gamma_fun. intros ast' st' Hstore'.
      simpl. apply bind_state_sound.
      * unfold sound. intros st'' ast'' Hstore''. simpl. apply IHa2. 
        apply Hstore''.
      * unfold sound. intros n' p' Hpar'. simpl. unfold gamma_fun.
        intros ast'' st'' Hstore''. simpl. unfold gamma_pairs;simpl;split.
        { apply sound_parity_mult; assumption. }
        { apply Hstore''. }
      * apply Hstore'.
    + apply Hstore.
Qed.

Lemma eval_bexp_beq_sound : forall n n',
sound (eval_aexp n) (abstract_eval_aexp n) ->
sound (eval_aexp n') (abstract_eval_aexp n') ->
sound (eval_bexp (BEq n n')) (beval_abstract (BEq n n')).
Proof. 
  unfold sound. simpl. intros a a' IH1 IH2 st ast Hstore. simpl. 
  bind.
  unfold sound. intros n p Hpar. simpl. unfold gamma_fun.
  intros ast' st' Hstore'. simpl. bind. 
  unfold sound. intros n' p' Hpar'. simpl. unfold gamma_fun.
  intros ast'' st'' Hstore''. simpl. unfold gamma_pairs;simpl;split.
  apply sound_parity_eq. assumption. assumption. assumption.
Qed.

Lemma eval_bexp_ble_sound : forall n n', 
sound (eval_aexp n) (abstract_eval_aexp n) ->
sound (eval_aexp n') (abstract_eval_aexp n') ->
sound (eval_bexp (BLe n n')) (beval_abstract (BLe n n')).
Proof. 
  intros a a' H1 H2. simpl. apply bind_state_sound. assumption.
  unfold sound. intros n p Hpar. simpl. unfold gamma_fun. intros ast st Hstore.
  simpl. bind. unfold sound. intros n' p' Hpar'. simpl. unfold gamma_fun. 
  intros ast' st' Hstore'. simpl. pairs; auto.
Qed.

Lemma eval_bexp_not_sound : forall b,
sound (eval_bexp b) (beval_abstract b) ->
sound (eval_bexp (BNot b)) (beval_abstract (BNot b)).
Proof. 
  intros b H.
  unfold sound. intros st ast Hstore. simpl. bind.
  unfold sound. intros b' ab Hbool. simpl. unfold gamma_fun. 
    intros aast' st' Hstore'. pairs.
    + apply sound_ab_neg. apply Hbool.
    + apply Hstore'.
Qed.

Lemma eval_bexp_and_sound : forall b1 b2,
sound (eval_bexp b1) (beval_abstract b1) ->
sound (eval_bexp b2) (beval_abstract b2) ->
sound (eval_bexp (BAnd b1 b2)) (beval_abstract (BAnd b1 b2)).
Proof. 
  intros b1 b2 H1 H2. unfold sound. intros st ast Hstore.
  simpl. bind. unfold sound. intros b ab Hbool. simpl. unfold gamma_fun.
    intros ast' st' Hstore'. simpl. bind.
    + unfold sound. intros b' ab' Hbool'. simpl. unfold gamma_fun.
      intros ast'' st'' Hstore''. simpl. pairs.
      * apply sound_ab_and; assumption.
      * assumption.
Qed.

Theorem eval_bexp_sound :
  forall b, sound (eval_bexp b) (beval_abstract b).
Proof.
  induction b.
  - simpl. unfold sound. intros st ast Hstore. simpl. 
    unfold gamma_pairs; simpl; split; auto.
  - simpl. unfold sound. intros st ast Hstore. simpl.
    unfold gamma_pairs; simpl; split; auto.
  - apply eval_bexp_beq_sound; apply eval_aexp_sound.
  - apply eval_bexp_ble_sound; apply eval_aexp_sound.
  - apply eval_bexp_not_sound. apply IHb.
  - apply eval_bexp_and_sound; assumption.
Qed.

Lemma sound_seq : forall c1 c2,
  sound (ceval c1) (ceval_abstract c1) ->
  sound (ceval c2) (ceval_abstract c2) ->
  sound (ceval (c1 ;c; c2)) (ceval_abstract (c1 ;c; c2)).
Proof.
  intros c1 c2 H1 H2. unfold sound. intros. simpl. bind.
  unfold sound. intros. simpl. unfold gamma_fun. intros.
    unfold sound in H2. apply H2. apply H3.
Qed.

Lemma sound_assignment : forall x a,
  sound (ceval (CAss x a)) (ceval_abstract (CAss x a)).
Proof. 
  intros. unfold sound. intros. bind.
  - apply eval_aexp_sound.
  - simpl. unfold sound. intros. simpl. unfold gamma_fun. intros.
    simpl. unfold gamma_pairs. simpl. split.
    + constructor.
    + unfold gamma_store. intros x'. apply t_update_sound; assumption.
Qed.
  
Lemma sound_if : forall b c1 c2,
  sound (ceval c1) (ceval_abstract c1) ->
  sound (ceval c2) (ceval_abstract c2) ->
  sound (ceval (CIf b c1 c2)) (ceval_abstract (CIf b c1 c2)).
Proof. 
  intros. simpl. apply bind_state_sound. 
  - apply eval_bexp_sound.
  - unfold sound. intros. simpl. unfold gamma_fun. intros. simpl.
    unfold eval_if_abstract. unfold eval_if. destruct a.
    + destruct b0. apply H. apply H2. inversion H1.
    + destruct b0. 
      * simpl in *. unfold not in H1. exfalso. apply H1. reflexivity.
      * apply H0. apply H2.
    + admit. 
    + inversion H1.
Admitted.

Lemma sound_try_catch : forall c1 c2,
  sound (ceval c1) (ceval_abstract c1) ->
  sound (ceval c2) (ceval_abstract c2) ->
  sound (ceval (CTryCatch c1 c2)) (ceval_abstract (CTryCatch c1 c2)).
Proof.
  intros c1 c2 H1 H2. simpl. unfold sound. intros st ast Hstore.
  simpl. unfold eval_catch. destruct (ceval_abstract c1 ast) eqn:Habs1.
  - destruct (ceval c1 st) eqn:Hconc1. 
    + rewrite <- Habs1, <- Hconc1. unfold sound in H1. apply H1. assumption.
    + unfold sound in H1. simpl in H1. 
      assert (gamma_option (ceval_abstract c1 ast) (ceval c1 st)).
      { apply H1. apply Hstore. }
      rewrite Habs1 in H. rewrite Hconc1 in H. inversion H.
  - destruct (ceval c1 st) eqn:Hconc1. 
    + unfold sound in H1. simpl in *. 
      destruct (ceval_abstract c2 ast).
      * simpl. destruct p, p0. pairs.
        { reflexivity. }
        { admit. }
      * reflexivity.
    + apply H2. apply Hstore.
Admitted.

Theorem sound_interpreter:
  forall c, sound (ceval c) (ceval_abstract c).
Proof.
  intros. induction c; unfold sound; intros.
  - (* SKIP *) simpl in *. unfold gamma_pairs. simpl.
    split; auto; reflexivity.
  - (* Sequence *) apply sound_seq; assumption.
  - (* Assignment *) apply sound_assignment; assumption.
  - (* If *) apply sound_if; assumption.
  - (* Try-Catch *) apply sound_try_catch; assumption.
  - (* Fail *) reflexivity.
Qed.
