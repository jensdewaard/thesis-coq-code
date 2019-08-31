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

Tactic Notation "pairs" := unfold gamma_pairs; simpl; split;auto; try reflexivity.
Hint Extern 4 => pairs.

Arguments gamma : simpl never.
Arguments join_op : simpl never.
  
Definition sound_store (ast : abstract_store) (st : store) : Prop := 
  forall x, gamma (ast x) (st x).
Hint Unfold sound_store.

Lemma return_state_sound {A B : Type} `{Galois A B} :
  gamma (return_state_abstract B) (return_state A).
Proof. 
  intros ???. unfold gamma. simpl.
  intros ???. unfold gamma. simpl. auto.
Qed.

Lemma t_update_sound : forall (ast : abstract_store) (st : store) x p n,
  gamma ast st ->
  gamma p n ->
  gamma (t_update ast x p) (t_update st x n).
Proof. 
  intros. unfold t_update.
  intro x'.
  destruct (beq_string x x'); auto.
Qed.

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
        { split. auto. simpl in Hstore. destruct Hstore.
          eapply H4 in H5. rewrite Hnext1 in H5. 
          rewrite Hnext2 in H5. simpl in H5. destruct H5.
          apply H5. auto. }
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5. 
          rewrite Hnext2 in H5. inversion H5. auto. }
        { auto. }
      * reflexivity.
      * simpl. destruct (next a1 s) eqn:Hnext2.
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5.
          rewrite Hnext2 in H5. inversion H5. auto. }
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5. 
          rewrite Hnext2 in H5. inversion H5. auto. }
        { auto. }
      * destruct (next a1 s) eqn:Hnext2. 
        { split. auto. destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5.
          rewrite Hnext2 in H5. destruct H5. auto. auto. }
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5. rewrite Hnext2 in
          H5. inversion H5. auto. }
        { auto. }
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

Hint Resolve bind_state_sound.

Tactic Notation "bind" := apply bind_state_sound;auto;try reflexivity.
Hint Extern 4 => bind.

Lemma sound_parity_plus :
  gamma parity_plus plus.
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct a, a0; simpl in *; try tauto;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.
Hint Extern 5 => apply sound_parity_plus.

Lemma sound_parity_mult :
  gamma parity_mult mult.
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct a, a0; simpl in *; try tauto; 
  auto using even_mult_l, even_mult_r, odd_mult.
Qed.
Hint Extern 5 => apply sound_parity_mult.

Lemma sound_parity_eq :
  gamma parity_eq Nat.eqb. 
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct a, a0; simpl in *; try tauto; unfold not; intros.
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd. 
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd.
Qed.
Hint Extern 5 => apply sound_parity_eq.

Lemma sound_ab_and :
  gamma and_ab andb.
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct b, b0, a, a0; simpl in *; auto.
Qed.
Hint Extern 5 => apply sound_ab_and.

Lemma sound_ab_or :
  gamma or_ab orb.
Proof. intros ? ? ? ? ? ?. unfold gamma.
  destruct b, b0, a, a0; simpl in *; auto.
Qed.
Hint Extern 5 => apply sound_ab_or.

Lemma sound_ab_neg :
  gamma neg_ab negb.
Proof. intros ? ? ?. unfold gamma.
  destruct b, a; simpl in *; auto.
Qed.
Hint Extern 5 => apply sound_ab_neg.

Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof. intros ? ? ? ? ? ?.
  simpl. destruct a, b; simpl; auto. 
Qed. 
Hint Extern 5 => apply ensure_par_sound.

Lemma ensure_abool_sound :
  gamma ensure_abool ensure_bool.
Proof. intros ? ? ? ? ? ?. 
  simpl. destruct a, b; simpl; auto.
Qed.
Hint Extern 5 => apply ensure_abool_sound.

Lemma pplusM_sound : gamma pplusM plusM.
Proof.
  intros p1 i1 ? p2 i2 ? ? ? ?. pairs. 
Qed.
Hint Extern 5 => apply pplusM_sound. 

Lemma extract_bool_sound : forall ast st x,
  gamma ast st ->
  gamma (extract_ab x ast) (extract_boolean x st).
Proof.
  intros ast st b H. unfold gamma. simpl. 
  destruct b; unfold gamma; auto. simpl; unfold gamma; simpl.
  auto. 
Qed.
Hint Extern 5 => apply extract_bool_sound.

Hint Unfold gamma_fun.
Hint Unfold gamma_store.
Hint Unfold shared_eval_expr.
Theorem eval_expr_sound :
  forall a, gamma (eval_expr_abstract a) (eval_expr a).
Proof.
  intros. unfold eval_expr, eval_expr_abstract. induction a.
  - (* (* ENum *) simpl. unfold sound. intros. unfold gamma_result. 
    unfold extract_build_val.
    destruct c; simpl. split. apply gamma_par_extract_n_n. apply H.
    destruct b0; simpl; auto. *) simpl. intros ? ? ?. simpl. 
    destruct c. simpl. pairs. apply gamma_par_extract_n_n. simpl. 
    bind. intros ? ? ?.  auto. 
  - (* EVar *) simpl. pairs. 
  - (* EPlus *) simpl in *. bind. 
    intros v1 av1 Hav1. bind.
    intros v2 av2 Hav2. bind.
    intros ? ? ?.  bind. 
  - (* EMult *)
    simpl in *. bind. 
    intros v1 av1 Hav1. bind. 
    intros v2 av2 Hav2. bind. 
    intros n1 an1 Han1. bind. 
  - (* EEq *)
    bind. intros v1 av1 Hav1. bind. 
    intros v2 av2 Hav2. bind.
    intros n1 an1 Han1. bind. 
  - (* ELe *)
    bind. intros ? ? ?. bind. intros ? ? ?. bind. 
    intros ? ? ?. bind. 
  - (* ENot *)
    bind. intros ? ? ?. bind.
  - (* EAnd *) bind. intros ? ? ?. bind. intros ???. bind.
    intros ???. bind.
Qed.
Hint Resolve eval_expr_sound.

Lemma sound_store_put : forall s,
  gamma (abstract_store_put s) (store_put s).
Proof. 
  intros ???? ???. unfold abstract_store_put, store_put. unfold gamma.
  simpl. split. constructor. apply t_update_sound; auto.
Qed.

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

Lemma sound_fail : 
  gamma fail_abstract fail.
Proof.
  unfold fail_abstract, fail. intros ???. auto.
Qed.

Theorem sound_interpreter:
  forall c, gamma (ceval_abstract c) (ceval c).
Proof.
  intros. unfold ceval_abstract, ceval. induction c.
  - (* SKIP *)
    simpl. apply return_state_sound. constructor.
  - (* SEQ *)
    simpl. bind. intros ???. apply IHc2.
  - (* Assignment *)
    simpl. bind. intros ???. apply sound_store_put. assumption.
  - (* CIf *)
    simpl. bind. intros ???. bind. intros ???. apply sound_if_op; assumption.
  - (* TryCatch *)
    simpl. apply sound_eval_catch; assumption.
  - simpl. apply sound_fail.
Qed.

Open Scope com_scope.

Definition program1 := 
  IF2 (ELe (EVal (VNat 5)) (EVal (VNat 4))) 
  THEN (CAss "x" (EVal (VBool true))) 
  ELSE (CAss "x" (EVal (VNat 9))).
  
Lemma sound_program1 : 
  gamma (ceval_abstract program1) (ceval program1).
Proof.
  simpl. auto.
Qed.

Definition program2 :=
  CAss "x" (EVal (VNat 20)) ;c;
  IF2 (EEq (EVar "x") (EVal (VNat 10)))
  THEN CThrow
  ELSE (CAss "x" (EVal (VNat 20))).

Lemma sound_program2 :
  gamma (ceval_abstract program2) (ceval program2).
Proof. 
  intros. simpl. auto.
Qed.

Definition program2' :=
  CAss "x" (EVal (VNat 20)) ;c;
  IF2 (EEq (EVar "x") (EVal (VNat 9)))
  THEN CThrow
  ELSE (CAss "x" (EVal (VNat 20))).

Lemma sound_program2' :
  gamma (ceval_abstract program2') (ceval program2').
Proof. 
  split.
  - auto.
  - intro. simpl. 
    apply t_update_sound. apply t_update_sound. apply H. 
    repeat constructor.
    repeat constructor.
Qed.

Definition program3 :=
  CAss "x" (EPlus (EVal (VNat 10)) (EVal ((VBool true)))).
  
Lemma sound_program3 :
  gamma (ceval_abstract program3) (ceval program3).
Proof. simpl.  auto. Qed.

