Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractInterpreter.
Require Import Classes.Galois.
Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import ConcreteInterpreter.
Require Import Instances.Except.AbstractException.
Require Import Instances.Except.ConcreteException.
Require Import Instances.Galois.AbstractState.
Require Import Instances.Galois.AbstractStore.
Require Import Instances.Galois.Functions.
Require Import Instances.Galois.Pairs.
Require Import Instances.Galois.Parity.
Require Import Instances.Galois.Result.
Require Import Instances.Galois.Unit.
Require Import Instances.Galois.Values.
Require Import Instances.IsBool.AbstractBoolean.
Require Import Instances.IsBool.Boolean.
Require Import Instances.IsNat.Nat.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.AbstractStore.
Require Import Instances.Store.AbstractStore.
Require Import Instances.Store.ConcreteStore.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.State.
Require Import Types.Stores.

Create HintDb soundness.

Arguments gamma : simpl never.
Arguments join_op : simpl never.
  
(* Soundness of unit *)

Lemma gamma_unit_sound :
  gamma tt tt.
Proof. constructor. Qed.
Hint Resolve gamma_unit_sound : soundness.

(* Soundness of parity operations *)

Lemma parity_plus_sound :
  gamma parity_plus plus.
Proof. intros ? ? ? ? ? ?. unfold gamma; simpl. 
  destruct a, a0; simpl in *; try tauto;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.
Hint Resolve parity_plus_sound : soundness.

Lemma parity_mult_sound :
  gamma parity_mult mult.
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct a, a0; simpl in *; try tauto; 
  auto using even_mult_l, even_mult_r, odd_mult.
Qed.
Hint Resolve parity_mult_sound : soundness.

Lemma parity_eq_sound :
  gamma parity_eq Nat.eqb. 
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct a, a0; simpl in *; try tauto; unfold not; intros.
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd. 
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd.
Qed.
Hint Resolve parity_eq_sound : soundness.

Lemma extract_par_sound : forall n,
  gamma (VParity (extract_par n)) (VNat n).
Proof. 
  apply gamma_par_extract_n_n.
Qed.
Hint Resolve gamma_par_extract_n_n : soundness.
Hint Resolve extract_par_sound : soundness.

(* Monadic versions of parity operations *)

Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof. intros p n ????. unfold gamma in *; simpl in *.
  destruct p, n; simpl; auto. 
Defined. 
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound :  forall n,
  gamma (extract_parM n) (return_state nat n). 
Proof.
  intros. unfold gamma; simpl. intros ???. unfold gamma; simpl.
  split. apply extract_par_sound. assumption.
Qed.
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound : 
  gamma pplusM plusM.
Proof.
  intros p1 i1 ? p2 i2 ? ? ? ?. constructor. 
  apply parity_plus_sound; assumption. assumption.
Qed.
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound :
  gamma pmultM multM.
Proof.
  intros p1 i1 ? p2 i2 ? ? ? ?. constructor. 
  apply parity_mult_sound; assumption. assumption.
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound :
  gamma peqM eqbM.
Proof.
  intros p1 i1 ? p2 i2 ? ? ? ?. constructor. 
  apply parity_eq_sound; assumption. assumption.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound :
  gamma pleM lebM.
Proof.
  intros ?????????. constructor. reflexivity. assumption.
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound :
  gamma build_parity build_natural.
Proof.
  intros ??????. split. apply H. apply H0.
Qed.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on booleans *)

Lemma ab_and_sound :
  gamma and_ab andb.
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct b, b0, a, a0; simpl in *; auto.
Qed.

Lemma ab_or_sound :
  gamma or_ab orb.
Proof. intros ? ? ? ? ? ?. unfold gamma; simpl.
  destruct b, b0, a, a0; simpl in *; auto.
Qed.
Hint Resolve ab_or_sound : soundness.

Lemma ab_neg_sound :
  gamma neg_ab negb.
Proof. intros ? ? ?. unfold gamma in *; simpl in *.
  destruct b, a; simpl in *; auto.
Qed.
Hint Resolve ab_neg_sound.

Lemma extract_bool_sound : forall x,
  gamma (VAbstrBool (extract_ab x)) (VBool x).
Proof.
  intros b. destruct b. simpl. constructor. simpl. unfold gamma; simpl.
  unfold gamma; simpl. unfold not. intro. assumption.
Qed.
Hint Resolve extract_bool_sound : soundness.

(* Monadic operations on abstract booleans *)

Lemma ensure_abool_sound :
  gamma ensure_abool ensure_bool.
Proof. intros ab b ? ? ? ?. 
  unfold gamma in *; simpl in *. destruct ab, b; simpl; auto.
Qed.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound :
  gamma neg_abM negbM.
Proof.
  intros ??????. constructor. apply neg_ab_sound. assumption. assumption.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound :
  gamma and_abM andbM.
Proof.
  intros ?????????. constructor. apply and_ab_sound; assumption. assumption.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound: forall b,
  gamma (extract_abM b) (return_state bool b).
Proof. 
  intros. unfold gamma in *; simpl in *. destruct b; auto. intros ???. 
  split; auto. constructor. intros ???. constructor. unfold gamma; simpl.
  unfold not. intro. assumption. assumption.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound :
  gamma build_abool build_bool.
Proof.
  intros ??????. split. apply H. apply H0.
Qed.
Hint Resolve build_boolean_sound : soundness.

(* Soundness of applied functions *)

Lemma functions_sound {A A' B B'} `{Galois A A', Galois B B'}
  (f : A -> B) (f' : A' -> B') x x' :
  gamma f' f -> gamma x' x ->
  gamma (f' x') (f x).
Proof. intros Hf ?. apply Hf. assumption. Qed.
Hint Resolve functions_sound : soundness.

(* Soundness of operations on stores *)

Lemma store_get_sound : forall s,
  gamma (abstract_store_get s) (store_get s).
Proof.
  intros s. intros ???. unfold store_get, abstract_store_get.
  unfold gamma; simpl. split; apply H.
Qed.
Hint Resolve store_get_sound : soundness.

Lemma t_update_sound : forall (ast : abstract_store) (st : store) x p n,
  gamma ast st ->
  gamma p n ->
  gamma (t_update ast x p) (t_update st x n).
Proof. 
  intros. unfold t_update. intro x'.
  destruct (beq_string x x'); auto.
Qed.

Lemma store_put_sound : forall s,
  gamma (abstract_store_put s) (store_put s).
Proof. 
  intros ???? ???. unfold abstract_store_put, store_put. unfold gamma.
  simpl. split. constructor. apply t_update_sound; auto.
Qed.
Hint Resolve store_put_sound : soundness.

(* Soundness of states *)

Lemma return_state_sound {A B : Type} `{Galois A B} :
  gamma (return_state_abstract B) (return_state A).
Proof. 
  intros ???. constructor; auto. 
Qed.
Hint Resolve return_state_sound : soundness.

Lemma bind_state_sound {A A' B B'} 
`{Galois A A', Galois B B'}
: 
forall next next' f f',
gamma f' f ->
gamma next' next ->
gamma (bind_state_abstract A' B' f' next') (bind_state A B f next).
Proof.
  intros. 
  unfold bind_state, bind_state_abstract.  
  intros ast st Hstore. apply H3 in Hstore.
  simpl in Hstore. 
  destruct (f' ast) eqn:Hfa.
  - destruct (f st).
    + (* both return a value *)
      apply H4; apply Hstore.
    + (* concrete crashes *) inversion Hstore.
    + (* concrete throws exception *) inversion Hstore.
  - reflexivity.
  - destruct (f st).
    + inversion Hstore.
    + inversion Hstore.
    + apply Hstore.
  - destruct (f st) eqn:Hfb.
    + unfold result_doorgeven. 
      destruct (next' a a0) eqn:Hnext1.
      * simpl. destruct (next a1 s) eqn:Hnext2. 
        { constructor. constructor. destruct Hstore.
          eapply H4 in H5. rewrite Hnext1 in H5. 
          rewrite Hnext2 in H5. destruct H5.
          apply H5. auto. }
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5. 
          rewrite Hnext2 in H5. inversion H5. auto. }
        { constructor. }
      * reflexivity.
      * simpl. destruct (next a1 s) eqn:Hnext2.
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5.
          rewrite Hnext2 in H5. inversion H5. auto. }
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5. 
          rewrite Hnext2 in H5. inversion H5. auto. }
        { constructor. }
      * destruct (next a1 s) eqn:Hnext2. 
        { constructor. constructor. destruct Hstore. 
          eapply H4 in H5. rewrite Hnext1 in H5.
          rewrite Hnext2 in H5. destruct H5. assumption. assumption. }
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5. 
          rewrite Hnext2 in H5. inversion H5. auto. }
        { constructor. }
    + inversion Hstore. 
    + destruct result_doorgeven eqn:Hdoor. 
      * (* doorgeven gives result, impossible *)
        pose proof result_doorgeven_output.
        unfold not in H5. exfalso. eapply H5. apply Hdoor. 
      * (* doorgeven crashes *)
        reflexivity. 
      * (* doorgeven gives certain exception *)
        intro. apply result_doorgeven_widens_store_exception in Hdoor. 
        inversion Hdoor. eapply widen. apply H5. apply Hstore.
      * (* doorgeven gives either exception or return *)
        intro. 
        apply result_doorgeven_widens_store_exception_or_result in Hdoor.
        eapply widen. inversion Hdoor. apply H5. apply Hstore. 
Qed. 
Hint Resolve bind_state_sound : soundness.

Lemma bind_state_sound_fun {A A' B B'} `{Galois A A', Galois B B'} : 
  forall next next' f f',
  gamma f' f ->
  (forall x x', gamma x' x -> gamma (next' x') (next x)) ->
  gamma (bind_state_abstract A' B' f' next') (bind_state A B f next).
Proof. 
  intros. apply bind_state_sound. assumption. 
  assert ((forall x x', gamma x' x -> gamma (next' x') (next x)) -> gamma next'
  next). 
  { intros Hnext ???. apply Hnext. assumption. }
  apply H5. assumption.
Qed.
Hint Resolve bind_state_sound_fun : soundness.

(* Soundness of interpreters *)

Lemma extract_build_val_sound : forall v,
  gamma (extract_build_val (M:=AbstractState) v) (extract_build_val v).
Proof.
  destruct v; simpl; eauto with soundness.
Qed.
Hint Resolve extract_build_val_sound : soundness.

Theorem eval_expr_sound : forall a,
  gamma (shared_eval_expr (M:=AbstractState) a) (shared_eval_expr a).
Proof.
  intros. induction a; simpl;
  eauto 30 with soundness. 
Qed.
Hint Resolve eval_expr_sound : soundness.

Lemma sound_if_op : forall a b s1 s1' s2 s2',
  gamma a b ->
  gamma s1' s1 ->
  gamma s2' s2 ->
  gamma (eval_if_abstract a s1' s2')
  (eval_if b s1 s2).
Proof.
  intros ?????????.
  destruct b; simpl. 
  - (* true *)
    destruct a; simpl. 
    + assumption.
    + unfold gamma in H; simpl in H. tauto.
    + eapply widen. apply join_upper_bound_left. assumption.
    + unfold gamma in H; simpl in H. tauto.
  - destruct a; simpl.
    + unfold gamma in H; simpl in H; tauto.
    + assumption.
    + eapply widen. apply join_upper_bound_right. assumption.
    + unfold gamma in H; simpl in H; tauto.
Qed.
Hint Resolve sound_if_op : soundness.

Lemma sound_eval_catch : forall s1' s1 s2' s2,
  gamma s1' s1 ->
  gamma s2' s2 ->
  gamma (eval_catch_abstract s1' s2') (eval_catch s1 s2).
Proof.
  intros ?????????. 
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

Lemma sound_fail : 
  gamma fail_abstract fail.
Proof.
  unfold fail_abstract, fail. intros ???. auto.
Qed.
Hint Resolve sound_fail : soundness.

Theorem sound_interpreter:
  forall c, gamma (shared_ceval (M:=AbstractState) c) (shared_ceval c).
Proof.
  induction c; simpl; eauto 30 with soundness.
Qed.

