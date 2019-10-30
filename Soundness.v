Require Import Classes.Galois.
Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.PeanoNat.
Require Import Instances.Except.AbstractException.
Require Import Instances.Except.ConcreteException.
Require Import Instances.Galois.
Require Import Instances.IsBool.AbstractBoolean.
Require Import Instances.IsBool.Boolean.
Require Import Instances.IsNat.Nat.
Require Import Instances.IsNat.Parity.
Require Import Instances.IsNat.Interval.
Require Import Instances.Joinable.
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

Lemma gamma_fun_apply {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') x x' :
  gamma f' f -> gamma x' x ->
  gamma (f' x') (f x).
Proof. intros ??. apply H3. apply H4. Qed.
Hint Resolve gamma_fun_apply : soundness.

Lemma gamma_fun_applied {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') :
      (forall x x', gamma x' x -> gamma (f' x') (f x)) ->
        gamma f' f.
Proof. intros Hf ???. apply Hf. assumption. Qed.

(* Soundness of parity operations *)

Lemma parity_plus_sound :
  gamma parity_plus plus.
Proof. intros ? ? ? ? ? ?. destruct a, a0; inversion H; subst; inversion H0;
  subst; constructor;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.

Lemma parity_mult_sound :
  gamma parity_mult mult.
Proof. intros ? ? ? ? ? ?. destruct a, a0; 
  inversion H; subst; inversion H0; subst;
  simpl in *; try tauto; 
  constructor; auto using even_mult_l, even_mult_r, odd_mult.
Qed.

Lemma parity_eq_sound :
  gamma parity_eq Nat.eqb. 
Proof. intros ? ? ? ? ? ?. 
  destruct a, a0; inversion H; inversion H0; subst; try constructor.
  - assert ((b =? b0) = false) as contra. 
    apply Nat.eqb_neq. unfold not. intros; subst. eauto using not_even_and_odd.
    rewrite contra. simpl. apply gamma_false. 
  - assert (b =? b0 = false) as contra. 
    apply Nat.eqb_neq. unfold not. intros; subst. 
    eauto using not_even_and_odd. rewrite contra. simpl. apply gamma_false.
Qed.

Lemma extract_par_sound : forall n,
  gamma (VParity (extract_par n)) (VNat n).
Proof. 
  apply gamma_par_extract_n_n.
Qed.
Hint Resolve gamma_par_extract_n_n : soundness.

(* Monadic versions of parity operations *)

Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof.
  apply gamma_fun_applied. intros. 
  destruct x'; try constructor. destruct x; try inversion H.
  constructor. constructor. constructor. assumption. 
  assumption. constructor. constructor. constructor. assumption. 
  assumption. constructor. constructor. constructor. assumption.
Qed.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound :  forall n,
  gamma (extract_parM n) (extract_natM n). 
Proof.
  intros. constructor. constructor. simpl.
  apply extract_par_sound. simpl. assumption.
Qed.
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound : 
  gamma pplusM plusM.
Proof. constructor. constructor; simpl.
  apply parity_plus_sound; assumption. assumption.
Qed.
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound :
  gamma pmultM multM.
Proof.
  constructor. constructor. apply parity_mult_sound; assumption. assumption.
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound :
  gamma peqM eqbM.
Proof.
  constructor. constructor.
  apply parity_eq_sound; assumption. assumption.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound :
  gamma pleM lebM.
Proof.
  constructor. constructor. constructor. assumption.
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound :
  gamma build_parity build_natural.
Proof.
  constructor. constructor; auto.
Qed.
Hint Resolve build_parity_sound : soundness.

Lemma iplus_sound : gamma Interval.iplus plus.
Proof.
  intros i n Hn j m Hm. destruct Hn as [Hin Hni].
  destruct Hm as [Hjm Hmj]. simpl in *. constructor. 
  - rewrite Interval.interval_min_plus. simpl.
    apply Coq.Arith.Plus.plus_le_compat; assumption.
  - rewrite Interval.interval_max_plus. simpl.
    apply Coq.Arith.Plus.plus_le_compat; assumption.
Qed.

(* Soundness of operations on intervals *)
Lemma iplusM_sound :
  gamma iplusM plusM.
Proof.
  constructor. constructor. constructor. apply iplus_sound; assumption.
  apply iplus_sound; assumption. assumption.
Qed.
Hint Resolve iplusM_sound : soundness.

Lemma imult_sound : gamma Interval.imult mult.
Proof.
  constructor. 
  - rewrite Interval.interval_min_mult. simpl.
    apply Coq.Arith.Mult.mult_le_compat. apply H. apply H0.
  - rewrite Interval.interval_max_mult. simpl.
    apply Coq.Arith.Mult.mult_le_compat. apply H. apply H0.
Qed.

Lemma imultM_sound :
  gamma imultM multM.
Proof.
  constructor. constructor.
  constructor. apply imult_sound. assumption. assumption.
  apply imult_sound; assumption. assumption.
Qed.
Hint Resolve imultM_sound.

Lemma ileqb_sound :
  gamma ileM lebM.
Proof.
  constructor. unfold Interval.ileqb. 
  destruct a, a0.  destruct H, H0. simpl in *.
  destruct (Interval.max (n, n0) <? Interval.min (n1, n2)) eqn:Hint.
  - rewrite Nat.ltb_lt in Hint. 
    assert (b <=b0). apply le_trans with (m:=Interval.max (n, n0)).
    assumption. apply lt_n_Sm_le. 
    apply lt_trans with (m:=Interval.min (n1, n2)). apply Hint.
    apply le_lt_n_Sm. assumption.
    apply Nat.leb_le in H3. rewrite H3. constructor. constructor. assumption.
  - apply Nat.ltb_nlt in Hint.
    destruct (Interval.max (n1, n2) <? Interval.min (n, n0)) eqn:Hint2.
    apply Nat.ltb_lt in Hint2.
    + assert (b <=? b0 = false).
      apply leb_correct_conv.
      apply le_lt_n_Sm in H2.
      eapply le_trans with (m:=S (Interval.max (n1, n2))). apply H2.
      apply lt_n_Sm_le. apply lt_n_S. 
      apply le_trans with (m:=Interval.min (n,n0)); assumption. 
      rewrite H3. constructor. apply gamma_false. assumption.
    + constructor. constructor. assumption.
Qed.
Hint Resolve ileqb_sound : soundness.

Lemma ieqM_sound : gamma ieqM eqbM.
Proof.
  constructor. 
  destruct H, H0. 
  unfold Interval.ieqb. 
  destruct (Interval.max a <? Interval.min a0) eqn:Hdiff.
  - assert (b =? b0 = false). apply Nat.eqb_neq. unfold not. intros. 
    subst. assert (preorder (Interval.min a0) (Interval.max a)).
    apply preorder_trans with (y:=b0); assumption.
    simpl in H3. apply Nat.ltb_ge in H3. rewrite H3 in Hdiff.
    discriminate.
    rewrite H3. constructor. apply gamma_false. assumption.
  - destruct (Interval.min a =? Interval.max a) eqn:Ha1; try reflexivity.
    destruct (Interval.max a =? Interval.min a0) eqn:Ha2; try reflexivity.
    destruct (Interval.min a0 =? Interval.max a0) eqn:Ha3; try reflexivity.
    simpl. rewrite Nat.eqb_eq in Ha1, Ha2, Ha3. 
    simpl in *. assert (b = b0). Nat.order.
    subst. rewrite Nat.eqb_refl. constructor. reflexivity. assumption.
    constructor. constructor. assumption. constructor. constructor.
    assumption. constructor. constructor. assumption.
Qed.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound :
  gamma build_interval build_natural.
Proof.
  constructor. constructor. assumption. assumption.
Qed.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound : forall n,
  gamma (extract_interval n) (extract_natM n).
Proof.
  intros n. constructor. constructor. constructor. 
  simpl. rewrite Interval.interval_min_refl. auto.
  simpl. rewrite Interval.interval_max_refl. auto.
  assumption.
Qed.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound : gamma ensure_interval ensure_nat.
Proof.
  apply gamma_fun_applied. intros. destruct x'; try constructor.
  destruct x. constructor. constructor; assumption. inversion H.
Qed.
Hint Resolve ensure_interval_sound : soundness.

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
Hint Resolve ab_neg_sound : soundness.

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
Proof. apply gamma_fun_applied. intros b ab H.
  destruct ab; try constructor. destruct b; try inversion H.
  constructor. constructor; assumption.
Qed.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound :
  gamma neg_abM negbM.
Proof.
  constructor. constructor. apply neg_ab_sound. assumption. assumption.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound :
  gamma and_abM andbM.
Proof.
  constructor. constructor. apply and_ab_sound; assumption. assumption.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound: forall b,
  gamma (extract_abM b) (extract_boolean b).
Proof. 
  intros. destruct b;
  repeat constructor. assumption.
  repeat constructor. apply gamma_false. assumption.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound :
  gamma build_abool build_bool.
Proof.
  repeat constructor; assumption.
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
  intros s. constructor. constructor. simpl. apply H. assumption.
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
  intros s. repeat constructor.
  simpl. apply t_update_sound; auto.
Qed.
Hint Resolve store_put_sound : soundness.

(* Soundness of states *)

Require Import Instances.Monad.

Check return_state.

(*Lemma return_state_sound {A B : Type} `{Galois A B} :
  gamma (return_state B) (return_state A).
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
gamma (@bind_state_abstract A' B' f' next') (@bind_state A B f next).
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
    + destruct (next' a a0) eqn:Hnext1.
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
    + destruct (next' a a0) eqn:Hnext; constructor.
Qed. 
Hint Resolve bind_state_sound : soundness.

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

(*
Lemma extract_build_val_sound : forall v,
  gamma (extract_build_val (M:=AbstractState) (A:=isnat_parity) v) 
        (extract_build_val v).
Proof.
  destruct v; simpl; eauto with soundness.
Qed.
Hint Resolve extract_build_val_sound : soundness.

Theorem eval_expr_sound : forall a,
  gamma (shared_eval_expr (M:=AbstractState) (A:=isnat_parity) a) 
        (shared_eval_expr (M:=State) a).
Proof.
  intros. induction a; simpl;
  eauto 30 with soundness. 
Qed.
Hint Resolve eval_expr_sound : soundness.

Lemma sound_if_op : 
  gamma (eval_if_abstract)
  (eval_if).
Proof.
  intros ????????????. 
  destruct b; simpl. 
  - (* true *)
    destruct a; simpl. 
    + apply H0. apply H2.
    + unfold gamma in H; simpl in H. tauto.
    + eapply widen. apply join_upper_bound_left. apply H0. apply H2.
    + unfold gamma in H; simpl in H. tauto.
  - destruct a; simpl.
    + unfold gamma in H; simpl in H; tauto.
    + apply H1. apply H2.
    + eapply widen. apply join_upper_bound_right. apply H1. apply H2.
    + unfold gamma in H; simpl in H; tauto.
Qed.
Hint Resolve sound_if_op : soundness.

Lemma sound_eval_catch :
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

Lemma sound_fail : 
  gamma fail_abstract fail.
Proof.
  unfold fail_abstract, fail. intros ???. auto.
Qed.
Hint Resolve sound_fail : soundness.

Theorem sound_interpreter:
  forall c, gamma (shared_ceval 
                    (M:=AbstractState) 
                    (A:=isnat_parity)
                    c) 
                  (shared_ceval c).
Proof.
  induction c; simpl; eauto 30 with soundness.
Qed.
*)
