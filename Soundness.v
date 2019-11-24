Require Export Base.
Require Export Instances.Galois.
Require Import Classes.Functor.
Require Import Classes.Galois.
Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.PeanoNat.
Require Import Instances.Except.
Require Import Instances.IsBool.AbstractBoolean.
Require Import Instances.IsBool.Boolean.
Require Import Instances.IsNat.Interval.
Require Import Instances.IsNat.Nat.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Instances.Store.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.Interval.
Require Import Types.State.
Require Import Types.Stores.

Arguments join_op : simpl never.

Hint Extern 5 (gamma ?A ?B) => constructor : soundness.
  
(* Soundness of unit *)

Lemma gamma_unit_sound :
  gamma tt tt.
Proof. eauto with soundness. Qed.
Hint Resolve gamma_unit_sound : soundness.

(* Soundness of functions *)

Lemma gamma_fun_apply {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') x x' :
  gamma f' f -> gamma x' x ->
  gamma (f' x') (f x).
Proof. eauto with soundness. Qed.
Hint Resolve gamma_fun_apply : soundness.

Lemma gamma_fun_applied {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') :
      (forall x x', gamma x' x -> gamma (f' x') (f x)) ->
        gamma f' f.
Proof. 
  intro. simpl; unfold gamma_fun. eauto with soundness. 
Qed.
Hint Resolve gamma_fun_applied : soundness.

(* Soundness of monadic operations *)
Section maybe_sound. 
  Lemma fmap_maybe_sound : gamma fmap_maybe fmap_maybe.
  Proof.
    intros ???. intros ???. unfold fmap_maybe. destruct a0, b0; 
    eauto with soundness.
  Qed.

  Lemma app_maybe_sound : gamma app_maybe app_maybe.
  Proof.
    intros ???. intros ???. destruct a, b, a0, b0; eauto with soundness. 
    simpl in *. apply H in H0. apply H0.
  Qed.

  Lemma bind_maybe_sound : ∀ f f' k k',
    gamma f f' → gamma k k' →
    gamma (bind_maybe f k) (bind_maybe f' k').
  Proof.
    intros ???. intros ???. unfold bind_maybe. destruct f, f'; 
    eauto with soundness. contradiction.
  Qed.
End maybe_sound.

Section maybeA_sound. 
  Lemma fmap_maybeA_sound : gamma fmap_abstract_maybe fmap_maybe.
  Proof.
    repeat intros ???. destruct a0, b0; simpl; eauto with soundness.
    simpl in H0. apply H in H0. apply H0.
    simpl in H0. apply H in H0. apply H0.
  Qed.

  Lemma app_maybeA_sound : gamma app_abstract_maybe app_maybe.
  Proof.
    repeat intros ???. destruct a, b, a0, b0; simpl in *; eauto with soundness;
    apply H; apply H0.
  Qed.

  Lemma bind_maybeA_sound {A A' B B'} `{Galois A' A, Galois B' B} :
    ∀ f f' x x', gamma f f' → gamma x x' →
    gamma (@bind_maybeA A B f x) (@bind_maybe A' B' f' x').
  Proof.
    intros. destruct f eqn:?, f' eqn:?; eauto with soundness. inv H3.
    - apply H4 in H3. simpl. destruct (x a) eqn:?.
      + destruct (x' a0); simpl in *; auto.
      + destruct (x' a0); simpl in *; auto.
      + reflexivity.
    - simpl; destruct (x a); reflexivity.
  Qed.
End maybeA_sound.

Instance galois_stateT {S M A B} `{PreorderedSet (StateT S M B)} : 
  Galois (StateT S M A) (StateT S M B).
Admitted.

Section stateT_sound.
  Check @fmap_stateT.

End stateT_sound.

Section state_sound.
  Context {S S' A A' B B'} `{Galois S S', Galois A A', Galois B B'}.

  Lemma fmap_state_sound : ∀ f' f k' k,
    gamma f' f → gamma k' k → 
    gamma (@fmap_state S' A' B' f' k') (@fmap_state S A B f k).
  Proof.
    intros. unfold fmap_state. intros ???.
    destruct (k' a) eqn:?, (k b) eqn:?. simpl in *. 
    apply H6 in H7. rewrite Heqp in H7.
    rewrite Heqp0 in H7. split. apply H5. apply H7. apply H7.
  Qed.

  Lemma app_state_sound : ∀ f' f k' k,
    gamma f' f → gamma k' k →
    gamma (@app_state S' A' B' f' k') (@app_state S A B f k).
  Proof.
    intros. unfold app_state. intros ???. 
    destruct (f' a) eqn:?. destruct (k' s) eqn:?. 
    destruct (f b) eqn:?. destruct (k s1) eqn:?.
    apply H5 in H7. rewrite Heqp, Heqp1 in H7.
    destruct H7. apply H6 in H8. rewrite Heqp0, Heqp2 in H8.  destruct H8.
    clear Heqp Heqp1 Heqp0 Heqp2.
    split. apply H7. apply H8. apply H9.
  Qed.

  Lemma bind_state_sound : ∀ f' f k' k,
    gamma f' f → gamma k' k →
    gamma (@bind_state S' A' B' f' k') (@bind_state S A B f k).
  Proof.
    unfold bind_state. repeat constructor. intros.
    simpl; unfold gamma_fun; intros.
    apply H5 in H7.
    destruct (f' a) eqn:Hfa, (f b) eqn:Hfb.
    apply H6; apply H7.
  Qed.
End state_sound.

(*Lemma lift_maybeAT_sound : gamma lift_maybeAT lift_maybeT.
  Proof.
  unfold lift_maybeAT, lift_maybeT. 
  intros ???. simpl. intros ???. simpl. apply bind_maybe_sound.
  apply bind_maybe_sound. auto.
  intros ???. destruct a1, b1. apply gamma_fun_applied.
  { intros. simpl. apply H2. }
  simpl. unfold fmap_maybe.
  simpl. apply fmap_sound. intros ???. 
  simpl in *. unfold bind_maybe.
  unfold gamma_maybe.
  apply H in H0.
  destruct (a a0).
  - destruct (b b0). 2: inv H0. destruct p eqn:?, p0 eqn:?.
    simpl in H0. destruct H0. simpl.
    simpl. 
    
  - destruct p eqn:?, p0 eqn:?. simpl in *. destruct H0. split.
    + unfold fmap_maybe. destruct m eqn:?. 
      * admit.
      * destruct a1. simpl in *. inv H0. simpl in H0.
  simpl; unfold gamma_fun; intros.
Admitted.
(*Require Import Instances.Monad.
Lemma return_state_sound :
  gamma (return_state) (return_state).
Proof.
  intros. constructor. intros. constructor. intros. constructor; assumption.
Qed.*)
*)
(* Soundness of parity operations *)

Lemma gamma_par_extract_n_n : forall n,
  gamma (extract_par n) n.
Proof.
  intros. autounfold with soundness. simpl. autounfold with soundness.
  destruct (Nat.even n) eqn:Hpar. 
  - rewrite Nat.even_spec in Hpar. assumption.
  - pose proof Nat.negb_even. 
    rewrite <- Nat.odd_spec. rewrite <- Nat.negb_even, Bool.negb_true_iff.
    assumption.
Qed.
Hint Resolve gamma_par_extract_n_n : soundness.

Lemma parity_plus_sound :
  gamma parity_plus plus.
Proof.
  apply gamma_fun_applied. intros. apply gamma_fun_applied. intros.
  unfold parity_plus. destruct x', x'0; simpl; eauto with soundness. 
Qed.
Hint Resolve parity_plus_sound : soundness.

Lemma parity_mult_sound :
  gamma parity_mult mult.
Proof. 
  simple_solve.
Qed.
Hint Resolve parity_mult_sound : soundness.

Hint Rewrite Nat.eqb_eq : soundness.
Lemma parity_eq_sound :
  gamma parity_eq Nat.eqb. 
Proof. 
  simple_solve.
Qed.
Hint Resolve parity_eq_sound : soundness.

Lemma extract_par_sound : forall n,
  gamma (VParity (extract_par n)) (VNat n).
Proof. 
  simple_solve. rewrite Nat.even_spec in Heqb. assumption.
  rewrite <- Nat.odd_spec. unfold Nat.odd. rewrite Heqb.
  reflexivity.
Qed.

(* Monadic versions of parity operations *)
Hint Unfold gamma : soundness.
Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof.
  unfold ensure_par, ensure_nat. intros ???. destruct a eqn:?, b eqn:?;
    try contradiction.
  - apply gamma_fun_apply. admit. eauto with soundness.
  - apply gamma_fun_apply. admit. eauto with soundness.
  - admit.
  - admit.
  - apply gamma_fun_apply. admit. eauto with soundness.
Admitted.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound :  forall n,
  gamma (extract_parM n) (extract_natM n). 
Proof. 
  intros. unfold extract_parM, extract_natM.  apply gamma_fun_apply.
  admit. eauto with soundness.
Admitted.
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound : 
  gamma pplusM plusM.
Proof. 
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold pplusM, plusM. apply gamma_fun_apply. 
  admit. eauto with soundness.
Admitted.
(*  repeat constructor; simpl; eauto with soundness.

  destruct H2. apply H2. destruct H1. apply H1.
Qed.*)
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound :
  gamma pmultM multM.
Proof.
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold pmultM, multM. apply gamma_fun_apply. admit.
  eauto with soundness.
  (*repeat constructor; simpl; eauto with soundness. 
  destruct H2; assumption.
  destruct H1; assumption.*)
Admitted.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound :
  gamma peqM eqbM.
Proof.
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold peqM, eqbM. apply gamma_fun_apply. admit.
  eauto with soundness.
Admitted.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound :
  gamma pleM lebM.
Proof.
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold pleM, lebM. apply gamma_fun_apply. admit.
  eauto with soundness.
Admitted.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound :
  gamma build_parity build_natural.
Proof.
  intros ???. 
  unfold build_parity, build_natural. apply gamma_fun_apply.
  admit. eauto with soundness.
Admitted.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on intervals *)
Lemma iplusM_sound :
  gamma iplusM plusM.
Proof. 
  intros ???. intros ???. unfold iplusM, plusM. apply gamma_fun_apply.
  admit. apply gamma_fun_apply. eauto with soundness.
Admitted.
Hint Resolve iplusM_sound : soundness.

Lemma imultM_sound :
  gamma imultM multM.
Proof.
  intros ???. intros ???. unfold imultM, multM. apply gamma_fun_apply.
  admit. eauto with soundness.
Admitted.
  (*
  repeat constructor; simpl; destruct H, H0.
  rewrite Interval.interval_min_mult;
  apply Coq.Arith.Mult.mult_le_compat; assumption.
  rewrite Interval.interval_max_mult;
  apply Coq.Arith.Mult.mult_le_compat; assumption.
  destruct H2; assumption.
  destruct H1; assumption.
*)
Hint Resolve imultM_sound.

Lemma ileqb_sound :
  gamma ileM lebM.
Proof.
  intros ???. intros ???. unfold ileM, lebM. apply gamma_fun_apply.
  admit. eauto with soundness.
Admitted.
Hint Resolve ileqb_sound : soundness.

Lemma ieqM_sound : gamma ieqM eqbM.
Proof.
  intros ???. intros ???. unfold ieqM, eqbM.
  apply gamma_fun_apply. admit.
  eauto with soundness.
Admitted.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound :
  gamma build_interval build_natural.
Proof.
  intros ???. unfold build_interval, build_natural.
  apply gamma_fun_apply. admit.
  eauto with soundness.
Admitted.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound : forall n,
  gamma (extract_interval n) (extract_natM n).
Proof.
  intros ?. unfold extract_interval, extract_natM.
  apply gamma_fun_apply. admit.
  simpl. unfold pure_stateT. intros ???. simpl.
  split.
  - eauto with soundness. admit.
  - eauto with soundness.
Admitted.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound : gamma ensure_interval ensure_nat.
Proof.
  intros ???. unfold ensure_interval, ensure_nat.
  destruct a, b; try contradiction.
  - admit. 
  - apply gamma_fun_apply. admit. eauto with soundness.
  - apply gamma_fun_apply. admit. eauto with soundness.
  - admit.
  - apply gamma_fun_apply. admit. eauto with soundness.
Admitted.
Hint Resolve ensure_interval_sound : soundness.

(* Soundness of operations on booleans *)

Lemma ab_and_sound :
  gamma and_ab andb.
Proof. 
  intros ???. intros ???. destruct a, a0, b, b0; eauto with soundness.
Qed.
Hint Resolve ab_and_sound : soundness.

Lemma ab_or_sound :
  gamma or_ab orb.
Proof. 
  intros ??????. destruct a, a0, b, b0; auto with soundness.
Qed.
Hint Resolve ab_or_sound : soundness.

Lemma ab_neg_sound :
  gamma neg_ab negb.
Proof. 
  intros ???. destruct a, b; eauto with soundness.
Qed.

Lemma extract_bool_sound : forall x,
  gamma (VAbstrBool (extract_ab x)) (VBool x).
Proof. 
  intros. destruct x; eauto with soundness.
Qed.
Hint Resolve extract_bool_sound : soundness.

(* Monadic operations on abstract booleans *)

Lemma ensure_abool_sound :
  gamma ensure_abool ensure_bool.
Proof. 
  intros ???. unfold ensure_abool, ensure_bool. 
  destruct a, b; eauto with soundness; try contradiction.
  apply gamma_fun_apply. admit. eauto with soundness.
Admitted.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound :
  gamma neg_abM negbM.
Proof.
  intros ???. unfold neg_abM, negbM. apply gamma_fun_apply.
  admit. apply gamma_fun_apply. eauto with soundness.
  destruct a, b; eauto with soundness.
Admitted.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound :
  gamma and_abM andbM.
Proof.
  intros ??????. unfold and_abM, andbM. apply gamma_fun_apply.
  admit. destruct a, b, a0, b0; eauto with soundness.
Admitted.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound: forall b,
  gamma (extract_abM b) (extract_boolean b).
Proof. 
  intro b. unfold extract_abM, extract_boolean. apply gamma_fun_apply.
  admit. destruct b; eauto with soundness.
Admitted.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound :
  gamma build_abool build_bool.
Proof.
  intros ???. unfold build_abool, build_bool.
Admitted.
Hint Resolve build_boolean_sound : soundness.

(* Soundness of applied functions *)

(*Lemma functions_sound {A A' B B'} `{Galois A A', Galois B B'}
  (f : A -> B) (f' : A' -> B') x x' :
  gamma f' f -> gamma x' x ->
  gamma (f' x') (f x).
Proof. apply gamma_fun_apply. Qed.
Hint Resolve functions_sound : soundness.*)

(* Soundness of operations on stores *)

(*Lemma store_get_sound : forall s,
  gamma (abstract_store_get s) (store_get s).
Proof.
  repeat constructor. inv H0. apply H1. inv H0; assumption.
  inv H; assumption.
Qed.
Hint Resolve store_get_sound : soundness.*)

Lemma t_update_sound : forall (ast : abstract_store) (st : store) x p n,
  gamma ast st ->
  gamma p n ->
  gamma (t_update ast x p) (t_update st x n).
Proof. 
  repeat constructor.
  unfold t_update. intros. simpl. unfold gamma_store. intro x'.
  destruct (beq_string x x'); auto. 
Qed.

(*Lemma store_put_sound : forall s,
  gamma (abstract_store_put s) (store_put s).
Proof. 
  repeat constructor; simpl.
  intros x. unfold t_update. destruct (beq_string s x). assumption.
  inv H1. apply H2. inv H0; assumption.
Qed.
Hint Resolve store_put_sound : soundness.
*)

(* Soundness of states *)
(*
Lemma bind_state_sound_fun {A A' B B'} `{Galois A A', Galois B B'} : 
  forall next next' f f',
  gamma f' f ->
  (forall x x', gamma x' x -> gamma (next' x') (next x)) ->
  gamma (@bind_state_abstract A' B' f' next') (@bind_state A B f next).
Proof. 
  intros. apply bind_state_sound. assumption. 
  assert ((forall x x', gamma x' x -> gamma (next' x') (next x)) -> gamma next'
  next). 
  { intros Hnext ???. apply Hnext. assumption. }
  apply H5. assumption.
Qed.
Hint Resolve bind_state_sound_fun : soundness.
*)

(* Soundness of interpreters *)
Arguments bindM : simpl never.
Arguments gamma : simpl never.

Lemma extract_build_val_sound : forall v,
  gamma (extract_build_val (M:=AbstractState) (A:=isnat_parity) v) 
        (extract_build_val (M:=ConcreteState) v).
Proof.
  destruct v; simpl. 
  - intros ???. apply gamma_fun_apply. unfold bindM. apply bind_maybeAT_sound.
  eauto with soundness.
Admitted.
Hint Resolve extract_build_val_sound : soundness.

Theorem eval_expr_sound : forall a,
  gamma (shared_eval_expr (M:=AbstractState) (A:=isnat_parity) a) 
        (shared_eval_expr (M:=ConcreteState) a).
Proof.
  intros. induction a; simpl.
  - eauto with soundness.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
Admitted.
Hint Resolve eval_expr_sound : soundness.

Lemma sound_if_op : 
  gamma (eval_if_abstract)
  (eval_if).
Proof.
  intros ????????????. 
  destruct b. 
  - (* true *)
    destruct a. 
    + apply H0. apply H2.
    + unfold gamma in H; simpl in H. contradiction.
    + unfold eval_if_abstract, eval_if. admit.
    + unfold gamma in H; simpl in H. contradiction.
  - destruct a; simpl.
    + unfold gamma in H; simpl in H; contradiction.
    + apply H1. apply H2.
    + apply H1. apply H2.
    + unfold gamma in H; simpl in H; contradiction.
Admitted.
Hint Resolve sound_if_op : soundness.

(*Lemma sound_eval_catch :
  gamma (eval_catch_abstract) (eval_catch).
Proof.
  intros s1' s1 H s2' s2. intros H0 a b H1. 
  unfold gamma in H, H0; simpl in H, H0; unfold gamma_fun in H, H0.
  unfold eval_catch_abstract, eval_catch.
  pose proof H1; apply H in H1.
  destruct (s1' a).
  - destruct (s1 b). 
    + apply H1.
    + apply H1.
    + inversion H1.
  - reflexivity.
  - destruct (s1 b).  
    + inversion H1.
    + inversion H1.
    + apply H0. apply H1.
  - destruct (s1 b).
    + eapply widen. apply join_upper_bound_left.
      apply H1.
    + inversion H1.
    + unfold gamma in H1; simpl in H1.
      eapply widen. apply join_upper_bound_right. unfold gamma; simpl.
      pose proof H1. apply H0 in H1.  apply H1.
Qed.
Hint Resolve sound_eval_catch : soundness.
*)
  (*
Lemma sound_fail : 
  gamma fail_abstract fail.
Proof.
  unfold fail_abstract, fail. intros ???. auto.
Qed.
Hint Resolve sound_fail : soundness.
*)

Theorem sound_interpreter:
  forall c, gamma (shared_ceval 
                    (M:=AbstractState) 
                    (A:=isnat_parity)
                    c) 
                  (shared_ceval (M:=ConcreteState) c).
Proof.
  induction c; simpl. eauto with soundness.
Admitted.

