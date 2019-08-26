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

  
Definition sound_store (ast : abstract_store) (st : store) : Prop := 
  forall x, gamma (ast x) (st x).
Hint Unfold sound_store.

Lemma t_update_sound : forall (ast : abstract_store) (st : store) x p n,
  gamma ast st ->
  gamma p n ->
  gamma (t_update ast x p) (t_update st x n).
Proof. 
  intros. simpl. unfold gamma_store, t_update.
  intro x'.
  destruct (beq_string x x'). 
  - assumption.
  - apply H.
Qed.

Lemma abstract_store_join_sound_left : forall ast1 ast2 st,
  gamma ast1 st ->
  gamma (abstract_store_join ast1 ast2) st.
Proof. 
  intros. unfold abstract_store_join. 
  constructor.
Qed.

Corollary abstract_store_join_sound_right : forall ast1 ast2 st,
  gamma ast2 st ->
  gamma (abstract_store_join ast1 ast2) st.
Proof.
  intros. unfold abstract_store_join. 
  constructor.
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
      simpl. apply H4. 
      apply Hstore. apply Hstore.
    + (* concrete crashes *) inversion Hstore.
    + (* concrete throws exception *) inversion Hstore.
  - reflexivity.
  - destruct (f st).
    + inversion Hstore.
    + inversion Hstore.
    + simpl. simpl in Hstore. apply Hstore.
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
      * simpl. destruct (next a1 s) eqn:Hnext2. 
        { split. auto. destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5.
          rewrite Hnext2 in H5. destruct H5. auto. auto. }
        { destruct Hstore. eapply H4 in H5. rewrite Hnext1 in H5. rewrite Hnext2 in
          H5. inversion H5. auto. }
        { auto. }
    + inversion Hstore. 
    + simpl in *. 
      destruct result_doorgeven eqn:Hdoor. 
      * (* doorgeven gives result, impossible *)
        pose proof result_doorgeven_output.
        unfold not in H5. exfalso. eapply H5. apply Hdoor. 
      * (* doorgeven crashes *)
        reflexivity. 
      * (* doorgeven gives certain exception *)
        simpl. unfold gamma_store. intro. unfold gamma_store in Hstore. 
        apply result_doorgeven_widens_store_exception in Hdoor. 
        inversion Hdoor. eapply widen. apply H5. apply Hstore.
      * (* doorgeven gives either exception or return *)
        simpl. unfold gamma_store. intro. unfold gamma_store in Hstore.
        apply result_doorgeven_widens_store_exception_or_result in Hdoor.
        eapply widen. inversion Hdoor. apply H5. apply Hstore. 
Qed. 

Hint Resolve bind_state_sound.

Tactic Notation "bind" := apply bind_state_sound;auto;try reflexivity.
Hint Extern 4 => bind.

Lemma sound_parity_plus :
  gamma parity_plus plus.
Proof. intros ? ? ? ? ? ?.
  destruct a, a0; simpl in *; try tauto;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.
Hint Extern 5 => apply sound_parity_plus.

Lemma sound_parity_mult :
  gamma parity_mult mult.
Proof. intros ? ? ? ? ? ?.
  destruct a, a0; simpl in *; try tauto; 
  auto using even_mult_l, even_mult_r, odd_mult.
Qed.
Hint Extern 5 => apply sound_parity_mult.

Lemma sound_parity_eq :
  gamma parity_eq Nat.eqb.
Proof. intros ? ? ? ? ? ?.
  destruct a, a0; simpl in *; try tauto; unfold not; intros.
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd. 
  - apply Bool.Is_true_eq_true in H1. apply Nat.eqb_eq in H1. subst.
    eauto using not_even_and_odd.
Qed.
Hint Extern 5 => apply sound_parity_eq.

Lemma sound_ab_and :
  gamma and_ab andb.
Proof. intros ? ? ? ? ? ?.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.
Hint Extern 5 => apply sound_ab_and.

Lemma sound_ab_or :
  gamma or_ab orb.
Proof. intros ? ? ? ? ? ?.
  destruct b, b0, a, a0; simpl in *; tauto.
Qed.
Hint Extern 5 => apply sound_ab_or.

Lemma sound_ab_neg :
  gamma neg_ab negb.
Proof. intros ? ? ?.
  destruct b, a; simpl in *; tauto.
Qed.
Hint Extern 5 => apply sound_ab_neg.

Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof. intros ? ? ? ? ? ?.
  simpl. destruct a, b; simpl; tauto. 
Qed. 
Hint Extern 5 => apply ensure_par_sound.

Lemma ensure_abool_sound :
  gamma ensure_abool ensure_bool.
Proof. intros ? ? ? ? ? ?. 
  simpl. destruct a, b; simpl; tauto.
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

Admitted.
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

Lemma sound_seq : forall c1 c2,
  gamma (ceval_abstract c1) (ceval c1) ->
  gamma (ceval_abstract c2) (ceval c2) ->
  gamma (ceval_abstract (c1 ;c; c2)) (ceval (c1 ;c; c2)).
Proof.
  intros c1 c2 H1 H2. bind. 
  intros ??????. auto. 
Qed.
Hint Resolve sound_seq.

Lemma sound_assignment : forall x a,
  gamma  (ceval_abstract (CAss x a)) (ceval (CAss x a)).
Proof. 
  intros. bind. 
  intros ???. simpl. intros ???. simpl. split; auto.
  unfold t_update. apply t_update_sound; auto.
Qed.
Hint Resolve sound_assignment.
  
Lemma sound_if : forall b c1 c2,
  gamma (ceval_abstract c1) (ceval c1) ->
  gamma (ceval_abstract c2) (ceval c2) ->
  gamma (ceval_abstract (CIf b c1 c2)) (ceval (CIf b c1 c2)).
Proof. 
  intros e c1 c2 H1 H2 cv av Hgamma.  simpl. 
  unfold ceval_abstract, ceval.
  simpl. bind. intros ??????. bind. intros ??????. 
  unfold eval_if_abstract, eval_if. destruct a1.
  - (* ab_true *) destruct b1.  apply H1. assumption. 
    inversion H3.
  - (* ab_false *) destruct b1. 
    + (* true, contradiction *) simpl in *. unfold not in H3. 
      exfalso. apply H3. reflexivity.
    + (* false *) apply H2. assumption.
  - (* ab_top *) destruct b1. 
    + (* true *)
      assert (preorder (ceval_abstract c1) (join_op (ceval_abstract c1)
      (ceval_abstract c2))).
      apply join_upper_bound_left.
      inversion H5; subst. unfold ceval_abstract in H6. 
      eapply widen. apply H6. auto.
    + (* false *) 
      assert (preorder (ceval_abstract c2) (join_op (ceval_abstract c1) (ceval_abstract c2))).
      apply join_upper_bound_right.
      inversion H5; subst. unfold ceval_abstract in H6.
      eapply widen. apply H6. auto.
  - (* ab_bottom *) inversion H3.
Qed.
Hint Resolve sound_if.

Lemma sound_try_catch : forall c1 c2,
  gamma (ceval_abstract c1) (ceval c1) ->
  gamma (ceval_abstract c2) (ceval c2) ->
  gamma (ceval_abstract (CTryCatch c1 c2)) (ceval (CTryCatch c1 c2)).
Proof.
  intros c1 c2 H1 H2 ast st Hstore. 
  pose proof Hstore.
  apply H1 in H.
  destruct (ceval_abstract c1) eqn:Habs1; 
  destruct (ceval c1) eqn:Hconc1.
  - eapply abs_trycatch_return in Habs1; rewrite Habs1. 
    eapply trycatch_return in Hconc1; rewrite Hconc1.
    apply H1. apply Hstore.
  - inversion H.
  - inversion H.
  - eapply abs_trycatch_crash in Habs1; rewrite Habs1. reflexivity.
  - eapply abs_trycatch_crash in Habs1; rewrite Habs1. reflexivity.
  - eapply abs_trycatch_crash in Habs1; rewrite Habs1. reflexivity.
  - inversion H.
  - inversion H.
  - eapply abs_trycatch_exception in Habs1; rewrite Habs1. 
    eapply trycatch_exception in Hconc1; rewrite Hconc1. apply H2. apply H.
  - eapply abs_trycatch_exceptreturn in Habs1; rewrite Habs1. 
    pose proof Hconc1.
    eapply trycatch_return in Hconc1; rewrite Hconc1. 
    simpl. destruct (shared_ceval c2); auto. simpl. 
    rewrite H0. auto.
  - inversion H.
  - simpl in H. 
    eapply abs_trycatch_exceptreturn in Habs1; rewrite Habs1. simpl.
    destruct (shared_ceval c2) eqn:Habs2; auto. simpl.
    eapply trycatch_exception in Hconc1; rewrite Hconc1. 
    destruct (ceval c2 s) eqn:Hconc2; auto. 
    apply H2 in Hstore. simpl in *. apply H2 in H.
    rewrite Hconc2 in H. 
    unfold ceval_abstract in H. rewrite Habs2 in H.
    inversion H.
Qed.
Hint Resolve sound_try_catch.

Lemma sound_fail : 
  gamma (ceval_abstract CThrow) (ceval CThrow).
Proof.
  intros b a H. simpl. apply H.
Qed.
Hint Resolve sound_fail.

Lemma sound_skip :
  gamma (ceval_abstract SKIP) (ceval SKIP).
Proof.
  simpl. split; auto. 
Qed.
Hint Resolve sound_skip.

Theorem sound_interpreter:
  forall c, gamma (ceval_abstract c) (ceval c).
Proof.
  intros. induction c; auto with soundness.
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
simpl. intros. split.
  - auto.
  - intro. simpl. 
    apply t_update_sound. apply t_update_sound. apply H. 
    simpl. repeat constructor.
    simpl. repeat constructor.
Qed.

Definition program3 :=
  CAss "x" (EPlus (EVal (VNat 10)) (EVal ((VBool true)))).
  
Lemma sound_program3 :
  gamma (ceval_abstract program3) (ceval program3).
Proof. simpl.  auto. Qed.

