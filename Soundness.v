Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractBool.
Require Import AbstractStore.
Require Import AbstractInterpreter.
Require Import ConcreteInterpreter.
Require Import PreorderedSet.
Require Import Galois.
Require Import GaloisInstances.
Require Import Joinable.
Require Import Statements.
Require Import Maps.
Require Import Monad.
Require Import Parity.
Require Import Preorder.
Require Import State.

Create HintDb soundness.

Tactic Notation "pairs" := unfold gamma_pairs; simpl; split;auto; try reflexivity.
Hint Extern 4 => pairs.

Definition sound {A B A' B' : Type} 
  `{Galois B A} `{Galois B' A'}
  (f : B->B') (f' : A->A') :=
  forall b a, gamma a b -> gamma (f' a) (f b).
Hint Unfold sound.
  
Definition sound_store (ast : abstract_store) (st : store) : Prop := 
  forall x, gamma (ast x) (st x).
Hint Unfold sound_store.

Lemma t_update_sound : forall ast st x p n,
  sound_store ast st ->
  gamma p n ->
  sound_store (t_update ast x p) (t_update st x n).
Proof. 
  intros. unfold sound_store.  intros. unfold t_update. 
  destruct (beq_string x x0). 
  - assumption.
  - unfold sound_store in H. apply H.
Qed.

Lemma abstract_store_join_sound_left : forall ast1 ast2 st,
  sound_store ast1 st ->
  sound_store (abstract_store_join ast1 ast2) st.
Proof. 
  unfold sound_store. intros. unfold abstract_store_join. 
  constructor.
Qed.

Corollary abstract_store_join_sound_right : forall ast1 ast2 st,
  sound_store ast2 st ->
  sound_store (abstract_store_join ast1 ast2) st.
Proof.
  unfold sound_store. intros. unfold abstract_store_join. 
  constructor.
Qed.

Lemma bind_state_sound {A A' B B'} 
`{Galois A A', Galois B B'}
: 
forall next next' f f',
sound f f' ->
sound next next' ->
sound (bind_state A B f next) (bind_state_abstract A' B' f' next').
Proof.
  intros. 
  unfold bind_state, bind_state_abstract. unfold sound. 
  intros. apply H3 in H5.
  simpl in H5.
  destruct (f' a).
  - destruct (f b).
    + simpl. destruct p. destruct p0. apply H4. 
      apply H5. apply H5.
    + inversion H5.
    + inversion H5.
  - reflexivity.
  - destruct (f b).
    + inversion H5.
    + inversion H5.
    + simpl. simpl in H5. apply H5.
Qed.

Hint Resolve bind_state_sound.

Tactic Notation "bind" := apply bind_state_sound;auto;try reflexivity.
Hint Extern 4 => bind.

Lemma sound_parity_plus :
  sound plus parity_plus.
Proof. intros ? ? ? ? ? ?.
  unfold sound. simpl. unfold gamma_fun; intros. simpl. 
  destruct a, a0; simpl in *; try tauto;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.
Hint Extern 5 => apply sound_parity_plus.

Lemma sound_parity_mult :
  sound mult parity_mult.
Proof. 
  unfold sound. simpl. unfold gamma_fun. intros. simpl.
  destruct a, a0; simpl in *; try tauto; 
  auto using even_mult_l, even_mult_r, odd_mult.
Qed.
Hint Extern 5 => apply sound_parity_mult.

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
Hint Extern 5 => apply sound_parity_eq.

Lemma sound_ab_and :
  sound andb and_ab.
Proof. 
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.
Hint Extern 5 => apply sound_ab_and.

Lemma sound_ab_or :
  sound orb or_ab.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.
Hint Extern 5 => apply sound_ab_or.

Lemma sound_ab_neg :
  sound negb neg_ab.
Proof.
  unfold sound. simpl. unfold gamma_fun. intros.
  destruct b, a; simpl in *; tauto.
Qed.
Hint Extern 5 => apply sound_ab_neg.

Lemma gamma_extract_n_n : forall v,
  gamma (extract v) v.
Proof.
  destruct v.
  - simpl. apply gamma_par_extract_n_n.
  - simpl. destruct b; simpl. reflexivity.
    unfold not. intros contra. inversion contra.
Qed.
Hint Extern 5 => apply gamma_extract_n_n.

Lemma ensure_par_sound : 
  sound ensure_nat ensure_par.
Proof.
  unfold sound. intros b a Hgamma.
  simpl. unfold gamma_fun. intros ast st Hstore. simpl.
  destruct a, b; try inversion Hgamma; pairs.
Qed.
Hint Extern 5 => apply ensure_par_sound.

Lemma ensure_abool_sound :
  sound ensure_bool ensure_abool.
Proof.
  unfold sound. intros b c Hgamma.
  simpl. unfold gamma_fun. intros ast st Hstore. simpl.
  destruct c, b; try inversion Hgamma; pairs.
Qed.
Hint Extern 5 => apply ensure_abool_sound.
  
Hint Unfold gamma_fun.
Hint Unfold gamma_store.
Theorem eval_expr_sound :
  forall a, sound (eval_expr a) (eval_expr_abstract a).
Proof.
  intros.
  unfold sound. simpl.
  induction a.
  - (* ENum *) simpl. pairs. 
  - (* EVar *) simpl. pairs. unfold gamma_store in H. apply H.
  - (* EPlus *) simpl in *. intros st ast H. bind. 
    unfold sound. intros n p Hgamma. simpl. unfold gamma_fun. 
    intros ast' st'. intros Hstore. simpl. bind.
    unfold sound. intros n' p' Hgamma'. simpl. unfold gamma_fun.
    intros ast'' st'' Hgamma''. simpl. bind.
    unfold sound. intros n'' p'' Hgamman''p''. simpl. unfold gamma_fun.
    intros ast''' st''' Hgamma_store'''. bind.
  - (* AMult *) intros st ast Hstore. simpl. 
    bind. intros n p Hpar. simpl. unfold gamma_fun. intros ast' st' Hstore'.
    simpl. bind.
    unfold sound. intros n' p' Hpar'. simpl. unfold gamma_fun.
    intros ast'' st'' Hstore''. simpl. bind.
    unfold sound. intros. simpl. auto.
  - (* EEq *)
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind.
  - (* ELe *)
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind.
  - (* ENot *)
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind.
  - (* EAnd *)
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind. unfold sound. intros. simpl. unfold gamma_fun.
    intros. simpl. bind.
Qed.
Hint Resolve eval_expr_sound.

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
  simpl. unfold sound. intros. simpl. unfold gamma_fun. intros.
  simpl. unfold gamma_pairs. simpl. split; auto.
  unfold gamma_store. intros x'. apply t_update_sound; assumption.
Qed.

Hint Resolve sound_assignment.
  
Lemma sound_if : forall b c1 c2,
  sound (ceval c1) (ceval_abstract c1) ->
  sound (ceval c2) (ceval_abstract c2) ->
  sound (ceval (CIf b c1 c2)) (ceval_abstract (CIf b c1 c2)).
Proof. 
  intros e c1 c2 H1 H2. simpl. bind.
  unfold sound. intros cv av Hgamma. simpl.
  unfold gamma_fun. intros. bind. unfold sound. intros.
  unfold eval_if_abstract. unfold eval_if. simpl in *. destruct a0.
  - (* ab_true *) destruct b0. unfold gamma_fun; intros. auto. 
    inversion H0.
  - (* ab_false *) destruct b0. 
    + (* true, contradiction *) simpl in *. unfold not in H0. 
      exfalso. apply H0. reflexivity.
    + (* false *) unfold gamma_fun;intros. apply H2. apply H3.
  - (* ab_top *) destruct b0.
    + (* true *)
      assert (preorder (ceval_abstract c1) (join_op (ceval_abstract c1) (ceval_abstract c2))).
      apply join_upper_bound_left.
      unfold gamma_fun; intros.
      simpl in H3. inversion H3; subst. 
      eapply widen. apply H5. auto.
    + (* false *) 
      assert (preorder (ceval_abstract c2) (join_op (ceval_abstract c1) (ceval_abstract c2))).
      apply join_upper_bound_right.
      unfold gamma_fun; intros.
      simpl in H3. inversion H3; subst.
      eapply widen. apply H5. auto.
  - (* ab_bottom *) inversion H0.
Qed.

Hint Resolve sound_if.

Lemma sound_try_catch : forall c1 c2,
  sound (ceval c1) (ceval_abstract c1) ->
  sound (ceval c2) (ceval_abstract c2) ->
  sound (ceval (CTryCatch c1 c2)) (ceval_abstract (CTryCatch c1 c2)).
Proof.
  intros c1 c2 H1 H2 st ast Hstore. 
  unfold sound in H1. apply H1 in Hstore.
  simpl. unfold eval_catch_abstract, eval_catch.
  destruct (ceval_abstract c1 ast) eqn:Habs1;
  destruct (ceval c1 st) eqn:Hconc1.
  - apply Hstore.
  - apply Hstore.
  - inversion Hstore.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - inversion Hstore.
  - inversion Hstore.
  - simpl in *. apply H2. apply Hstore.
Qed.

Hint Resolve sound_try_catch.

Lemma sound_fail : 
  sound (ceval CFail) (ceval_abstract CFail).
Proof.
  unfold sound. intros b a H. simpl. apply H.
Qed.

Hint Resolve sound_fail.

Lemma sound_skip :
  sound (ceval SKIP) (ceval_abstract SKIP).
Proof.
  simpl. split; auto. 
Qed.

Hint Resolve sound_skip.

Theorem sound_interpreter:
  forall c, sound (ceval c) (ceval_abstract c).
Proof.
  intros. induction c; auto with soundness.
Qed.
