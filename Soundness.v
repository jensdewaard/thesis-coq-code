Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractBool.
Require Import AbstractStore.
Require Import AbstractInterpreter.
Require Import ConcreteInterpreter.
Require Import Galois.
Require Import Joinable.
Require Import Language.
Require Import Maps.
Require Import Monad.
Require Import Parity.
Require Import Preorder.

Create HintDb soundness.

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
(*  intros. simpl. unfold gamma_fun. intros. simpl. unfold sound. intros b a H10.
  simpl. unfold bind_state. unfold sound in H8. 
  assert (gamma (f' a) (f b)); auto. 
  destruct (f' a) eqn:Hf'a; destruct (f b) eqn:Hfb. subst.
  destruct r, r0.
  - apply H9. simpl in H11. apply H11. apply H11.
  - unfold gamma_pairs. split.
    + simpl. destruct (fst (next' a0 s)); reflexivity.
    + simpl. 
  - inversion H11.
  - simpl.  destruct p. destruct (next a0 s); reflexivity.
  - reflexivity. 
Qed.
*)
Admitted.

Hint Resolve bind_state_sound.

Tactic Notation "bind" := apply bind_state_sound;auto;try reflexivity.

Tactic Notation "pairs" := unfold gamma_pairs; simpl; split;auto; try reflexivity.

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
  - (* ANum *) simpl. pairs. apply gamma_par_extract_n_n.
  - (* AVar *) simpl. pairs. unfold gamma_store in H. apply H.
  - (* APlus *) simpl in *. intros st ast H. bind.
    unfold sound. intros n p Hgamma. simpl. unfold gamma_fun. 
    intros ast' st'. intros Hstore. simpl. bind.
    unfold sound. intros n' p' Hgamma'. simpl. unfold gamma_fun.
    intros ast'' st'' Hgamma''. simpl. pairs.
    apply sound_parity_plus; assumption.
  - (* AMult *) intros st ast Hstore. simpl. 
    bind. intros n p Hpar. simpl. unfold gamma_fun. intros ast' st' Hstore'.
    simpl. bind.
    unfold sound. intros n' p' Hpar'. simpl. unfold gamma_fun.
    intros ast'' st'' Hstore''. simpl. pairs.
    apply sound_parity_mult; assumption.
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
  intros ast'' st'' Hstore''. simpl. pairs.
  apply sound_parity_eq. assumption. assumption.
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
  apply sound_ab_neg. apply Hbool.
Qed.

Lemma eval_bexp_and_sound : forall b1 b2,
sound (eval_bexp b1) (beval_abstract b1) ->
sound (eval_bexp b2) (beval_abstract b2) ->
sound (eval_bexp (BAnd b1 b2)) (beval_abstract (BAnd b1 b2)).
Proof. 
  intros b1 b2 H1 H2. unfold sound. intros st ast Hstore.
  simpl. bind. unfold sound. intros b ab Hbool. simpl. unfold gamma_fun.
  intros ast' st' Hstore'. simpl. bind.
  unfold sound. intros b' ab' Hbool'. simpl. unfold gamma_fun.
  intros ast'' st'' Hstore''. simpl. pairs.
  - apply sound_ab_and; assumption.
Qed.

Theorem eval_bexp_sound :
  forall b, sound (eval_bexp b) (beval_abstract b).
Proof.
  induction b.
  - simpl. unfold sound. intros st ast Hstore. simpl. 
    pairs.
  - simpl. unfold sound. intros st ast Hstore. simpl.
    pairs.
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

Hint Resolve sound_seq.

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

Hint Resolve sound_assignment.
  
Lemma sound_if : forall b c1 c2,
  sound (ceval c1) (ceval_abstract c1) ->
  sound (ceval c2) (ceval_abstract c2) ->
  sound (ceval (CIf b c1 c2)) (ceval_abstract (CIf b c1 c2)).
Proof. 
  intros. simpl. bind.
  { apply eval_bexp_sound. }
  unfold sound. intros. simpl.
  unfold eval_if_abstract. unfold eval_if. destruct a.
  - (* ab_true *) destruct b0. unfold gamma_fun; intros. apply H. apply H2. inversion H1.
  - (* ab_false *) destruct b0. 
    + (* true, contradiction *) simpl in *. unfold not in H1. 
      exfalso. apply H1. reflexivity.
    + (* false *) unfold gamma_fun;intros. apply H0. apply H2.
  - (* ab_top *) destruct b0.
    + (* true *)
      assert (preorder (ceval_abstract c1) (join_op (ceval_abstract c1) (ceval_abstract c2))).
      apply join_upper_bound_left.
      unfold gamma_fun; intros.
      simpl in H2. inversion H2; subst. 
      eapply widen. apply H4. auto.
    + (* false *) 
      assert (preorder (ceval_abstract c2) (join_op (ceval_abstract c1) (ceval_abstract c2))).
      apply join_upper_bound_right.
      unfold gamma_fun; intros.
      simpl in H2. inversion H2; subst.
      eapply widen. apply H4. auto.
  - (* ab_bottom *) inversion H1.
Qed.

Hint Resolve sound_if.

Lemma sound_try_catch : forall c1 c2,
  sound (ceval c1) (ceval_abstract c1) ->
  sound (ceval c2) (ceval_abstract c2) ->
  sound (ceval (CTryCatch c1 c2)) (ceval_abstract (CTryCatch c1 c2)).
Proof.
  intros c1 c2 H1 H2 st ast Hstore.  
  simpl. unfold eval_catch, eval_catch_abstract. 
  destruct (ceval_abstract c1 ast) eqn:Habs1;
  destruct (ceval c1 st) eqn:Hconc1. 
  - (* abstract eval and concrete eval succeed *) 
    rewrite <- Hconc1, <- Habs1. apply H1. apply Hstore.
  - (* abstract succeeds and concrete fails, contradiction *)
    unfold sound in H1. apply H1 in Hstore.
    rewrite Habs1 in Hstore. rewrite Hconc1 in Hstore. inversion Hstore.
  - (* abstract fails and concrete succeeds, should contradict?? *)
    unfold sound in H1. apply H1 in Hstore.
    simpl. unfold join_state. rewrite Habs1. reflexivity.
  - (* both fail *)
    simpl. unfold join_state. rewrite Habs1. simpl.
    destruct (ceval c2 st); reflexivity.
Qed.

Hint Resolve sound_try_catch.

Lemma sound_fail : 
  sound (ceval CFail) (ceval_abstract CFail).
Proof.
  unfold sound. reflexivity.
Qed.

Hint Resolve sound_fail.

Lemma sound_skip :
  sound (ceval SKIP) (ceval_abstract SKIP).
Proof.
  simpl. split; auto. simpl. reflexivity.
Qed.

Hint Resolve sound_skip.

Theorem sound_interpreter:
  forall c, sound (ceval c) (ceval_abstract c).
Proof.
  intros. induction c; auto with soundness.
Qed.
