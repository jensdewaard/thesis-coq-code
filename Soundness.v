Require Export Base.
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
Require Export Instances.Galois.
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


Arguments gamma : simpl never.
Arguments join_op : simpl never.

Hint Extern 5 (gamma ?A ?B) => constructor : soundness.
  
(* Soundness of unit *)

Lemma gamma_unit_sound :
  gamma tt tt.
Proof. eauto with soundness. Qed.
Hint Resolve gamma_unit_sound : soundness.

Lemma gamma_fun_apply {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') x x' :
  gamma f' f -> gamma x' x ->
  gamma (f' x') (f x).
Proof. Admitted.
(*
Proof. intros ??. constructor. apply H3. apply H4. Q *)
Hint Resolve gamma_fun_apply : soundness.


Lemma gamma_fun_applied {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') :
      (forall x x', gamma x' x -> gamma (f' x') (f x)) ->
        gamma f' f.
Proof. constructor. intros. apply H3. apply H4. Qed.
(*Hint Resolve gamma_fun_applied : soundness. *)

(*Require Import Instances.Monad.
Lemma return_state_sound :
  gamma (return_state) (return_state).
Proof.
  intros. constructor. intros. constructor. intros. constructor; assumption.
Qed.*)

(* Soundness of parity operations *)

Lemma gamma_par_extract_n_n : forall n,
  gamma (extract_par n) n.
Proof.
  intros. pose proof even_or_odd as Hpar. 
  destruct Hpar with (n:=n) as [Heven | Hodd].
  - rewrite even_extract_pareven; try constructor; assumption.
  - rewrite odd_extract_parodd; try constructor; assumption.
Qed.
Hint Resolve gamma_par_extract_n_n : soundness.

Lemma parity_plus_sound :
  gamma parity_plus plus.
Proof. repeat constructor. intros a' b' H'.  
  destruct a, a'; inversion H; subst; inversion H';
  subst; constructor;
  auto using even_even_plus, odd_plus_r, odd_plus_l, odd_even_plus.
Qed.
Hint Resolve parity_plus_sound : soundness.

Lemma parity_mult_sound :
  gamma parity_mult mult.
Proof. repeat constructor. intros a0 b0 H0. destruct a, a0; 
  inversion H; subst; inversion H0; subst;
  simpl in *; try tauto; 
  constructor; auto using even_mult_l, even_mult_r, odd_mult.
Qed.
Hint Resolve parity_mult_sound : soundness.

Lemma parity_eq_sound :
  gamma parity_eq Nat.eqb. 
Proof. repeat constructor. intros a0 b0 H0.
  destruct a, a0; inversion H; inversion H0; subst; try constructor.
  - assert ((b =? b0) = false) as contra. 
    apply Nat.eqb_neq. unfold not. intros; subst. eauto using not_even_and_odd.
    rewrite contra. simpl. apply gamma_false. 
  - assert (b =? b0 = false) as contra. 
    apply Nat.eqb_neq. unfold not. intros; subst. 
    eauto using not_even_and_odd. rewrite contra. simpl. apply gamma_false.
Qed.
Hint Resolve parity_eq_sound : soundness.

Lemma extract_par_sound : forall n,
  gamma (VParity (extract_par n)) (VNat n).
Proof. auto with soundness. Qed.

(* Monadic versions of parity operations *)

Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof.
  repeat constructor. intros.
  destruct a.
  - gamma_destruct; repeat constructor; gamma_destruct; try assumption.
  - gamma_destruct; repeat constructor; assumption.
  - gamma_destruct; repeat constructor; assumption.
  - gamma_destruct; repeat constructor; try assumption. 
    unfold ensure_par, ensure_nat. destr; repeat constructor; assumption.
  - gamma_destruct.
Qed.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound :  forall n,
  gamma (extract_parM n) (extract_natM n). 
Proof. repeat constructor; simpl; destruct H;
  auto with soundness. destruct H0. apply H0.
Qed.
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound : 
  gamma pplusM plusM.
Proof. 
  repeat constructor; simpl; eauto with soundness.
  destruct H2. apply H2. destruct H1. apply H1.
Qed.
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound :
  gamma pmultM multM.
Proof.
  repeat constructor; simpl; eauto with soundness. 
  destruct H2; assumption.
  destruct H1; assumption.
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound :
  gamma peqM eqbM.
Proof.
  repeat constructor; simpl. eauto with soundness.
  destruct H2; assumption.
  destruct H1; assumption.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound :
  gamma pleM lebM.
Proof.
  repeat constructor; simpl; eauto with soundness.
  destruct H2; assumption.
  destruct H1; assumption.
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound :
  gamma build_parity build_natural.
Proof.
  repeat constructor. assumption. 
  destruct H1; assumption.
  destruct H0; assumption.
Qed.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on intervals *)
Lemma iplusM_sound :
  gamma iplusM plusM.
Proof. 
  repeat constructor; simpl; destruct H, H0.
  rewrite Interval.interval_min_plus;
  apply Coq.Arith.Plus.plus_le_compat; assumption.
  rewrite Interval.interval_max_plus;
  apply Coq.Arith.Plus.plus_le_compat; assumption.
  destruct H2; assumption.
  destruct H1; assumption.
Qed.
Hint Resolve iplusM_sound : soundness.

Lemma imultM_sound :
  gamma imultM multM.
Proof.
  repeat constructor; simpl; destruct H, H0.
  rewrite Interval.interval_min_mult;
  apply Coq.Arith.Mult.mult_le_compat; assumption.
  rewrite Interval.interval_max_mult;
  apply Coq.Arith.Mult.mult_le_compat; assumption.
  destruct H2; assumption.
  destruct H1; assumption.
Qed.
Hint Resolve imultM_sound.

Lemma ileqb_sound :
  gamma ileM lebM.
Proof.
  repeat constructor; simpl. destruct H, H0. destruct i, i0. simpl in *.
  unfold Interval.ileqb.
  destruct (Interval.max (n1, n2) <? Interval.min (n3, n4)) eqn:Hint.
  - rewrite Nat.ltb_lt in Hint. 
    assert (n <=n0). apply le_trans with (m:=Interval.max (n1, n2)).
    assumption. apply lt_n_Sm_le. 
    apply lt_trans with (m:=Interval.min (n3, n4)). apply Hint.
    apply le_lt_n_Sm. assumption.
    apply Nat.leb_le in H5. rewrite H5. constructor. 
  - apply Nat.ltb_nlt in Hint.
    destruct (Interval.max (n3, n4) <? Interval.min (n1, n2)) eqn:Hint2.
    apply Nat.ltb_lt in Hint2.
    + assert (n <=? n0 = false).
      apply leb_correct_conv.
      apply le_lt_n_Sm in H4.
      eapply le_trans with (m:=S (Interval.max (n3, n4))). apply H4.
      apply lt_n_Sm_le. apply lt_n_S. 
      apply le_trans with (m:=Interval.min (n1,n2)); assumption. 
      rewrite H5. constructor. 
    + constructor. 
  - destruct H2; assumption.
  - destruct H1; assumption.
Qed.
Hint Resolve ileqb_sound : soundness.

Lemma ieqM_sound : gamma ieqM eqbM.
Proof.
  repeat constructor. simpl. destruct H, H0. 
  unfold Interval.ieqb. 
  destruct (Interval.max i <? Interval.min i0) eqn:Hdiff.
  - assert (n =? n0 = false). apply Nat.eqb_neq. unfold not. intros. 
    subst. assert (preorder (Interval.min i0) (Interval.max i)).
    apply preorder_trans with (y:=n0); assumption.
    simpl in *. apply Nat.ltb_ge in H5. rewrite H5 in Hdiff.
    discriminate.
    rewrite H5. constructor. 
  - destruct (Interval.min i =? Interval.max i) eqn:Ha1; try constructor.
    destruct (Interval.max i =? Interval.min i0) eqn:Ha2; try constructor.
    destruct (Interval.min i0 =? Interval.max i0) eqn:Ha3; try constructor.
    simpl. rewrite Nat.eqb_eq in Ha1, Ha2, Ha3. 
    simpl in *. assert (n = n0). Nat.order.
    subst. rewrite Nat.eqb_refl. constructor. 
  - destruct H2; assumption.
  - destruct H1; assumption.
Qed.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound :
  gamma build_interval build_natural.
Proof.
  repeat constructor; destruct H; try assumption.
  destruct H1; assumption.
  destruct H0; assumption.
Qed.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound : forall n,
  gamma (extract_interval n) (extract_natM n).
Proof.
  intros n. repeat constructor. 
  simpl. rewrite Interval.interval_min_refl. reflexivity. 
  rewrite Interval.interval_max_refl. reflexivity.
  destruct H0; assumption.
  destruct H; assumption.
Qed.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound : gamma ensure_interval ensure_nat.
Proof.
  repeat constructor. intros. destruct a;
  inv H; repeat constructor. destruct H0; assumption. destruct H0; assumption.
  destruct H2; assumption. destruct H2; assumption. destruct H; assumption.
  destruct H0; assumption. destruct b; repeat constructor; destruct H0;
  assumption.
Qed.
Hint Resolve ensure_interval_sound : soundness.

(* Soundness of operations on booleans *)

Lemma ab_and_sound :
  gamma and_ab andb.
Proof. 
  repeat constructor. intros. 
  destruct b, b0, a, a0; try constructor; try inv H; try inv H0.
Qed.

Lemma ab_or_sound :
  gamma or_ab orb.
Proof. repeat constructor; intros.
  destruct b, b0, a, a0; try constructor; try inv H; try inv H0.
Qed.
Hint Resolve ab_or_sound : soundness.

Lemma ab_neg_sound :
  gamma neg_ab negb.
Proof. repeat constructor. intros ? ? ?. 
  destruct a, b; try constructor; try inversion H.
Qed.

Lemma extract_bool_sound : forall x,
  gamma (VAbstrBool (extract_ab x)) (VBool x).
Proof. repeat constructor. destruct x; constructor. Qed.
Hint Resolve extract_bool_sound : soundness.

(* Monadic operations on abstract booleans *)

Lemma ensure_abool_sound :
  gamma ensure_abool ensure_bool.
Proof. repeat constructor. intros.
  destruct a; try constructor. destruct b; try inv H.
  repeat constructor. destruct H0; assumption. 
  inv H. repeat constructor. assumption. inv H; assumption.
  inv H0; assumption. destruct b; repeat constructor.
  inv H0; assumption. inv H0; assumption. destruct b; constructor.
  constructor. assumption. constructor. assumption. destruct b.
  constructor. constructor. assumption. constructor. constructor.
  assumption.
Qed.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound :
  gamma neg_abM negbM.
Proof.
  repeat constructor; simpl. apply gamma_fun_apply.
  apply ab_neg_sound. assumption. 
  inv H1; assumption. inv H0; assumption.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound :
  gamma and_abM andbM.
Proof.
  repeat constructor; simpl. repeat apply gamma_fun_apply.
  apply ab_and_sound. assumption. assumption. inv H2; assumption.
  inv H1; assumption.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound: forall b,
  gamma (extract_abM b) (extract_boolean b).
Proof. 
  repeat constructor; simpl. destruct b; constructor.
  inv H0; assumption. inv H; assumption.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound :
  gamma build_abool build_bool.
Proof.
  repeat constructor. assumption. inv H1; assumption.
  inv H0; assumption.
Qed.
Hint Resolve build_boolean_sound : soundness.

(* Soundness of applied functions *)

(*Lemma functions_sound {A A' B B'} `{Galois A A', Galois B B'}
  (f : A -> B) (f' : A' -> B') x x' :
  gamma f' f -> gamma x' x ->
  gamma (f' x') (f x).
Proof. apply gamma_fun_apply. Qed.
Hint Resolve functions_sound : soundness.*)

(* Soundness of operations on stores *)

Lemma store_get_sound : forall s,
  gamma (abstract_store_get s) (store_get s).
Proof.
  repeat constructor. inv H0. apply H1. inv H0; assumption.
  inv H; assumption.
Qed.
Hint Resolve store_get_sound : soundness.

Lemma t_update_sound : forall (ast : abstract_store) (st : store) x p n,
  gamma ast st ->
  gamma p n ->
  gamma (t_update ast x p) (t_update st x n).
Proof. 
  repeat constructor.
  unfold t_update. intro x'.
  destruct (beq_string x x'); auto. destruct H. apply H.
Qed.

Lemma store_put_sound : forall s,
  gamma (abstract_store_put s) (store_put s).
Proof. 
  repeat constructor; simpl.
  intros x. unfold t_update. destruct (beq_string s x). assumption.
  inv H1. apply H2. inv H0; assumption.
Qed.
Hint Resolve store_put_sound : soundness.

(* Soundness of states *)
Require Import Instances.Monad.
Lemma bind_state_sound {S S' A A' B B'} 
  `{Galois S S'}
  `{Galois A A', Galois B B'} : 
  forall f' f k' k,
  gamma f' f ->
  gamma k' k ->
  gamma (@bind_state S' A' B' f' k') (@bind_state S A B f k).
Proof.
  unfold bind_state. repeat constructor. intros.
  destruct (f' a) eqn:Hfa, (f b) eqn:Hfb.
  inv H5.
  destruct (k' a0 s) eqn:Hk', (k a1 s0) eqn:Hk.
  inv H6. apply H8 in H7. rewrite Hfa, Hfb in H7. inv H7.
  apply H5 in H11. inv H11. apply H6 in H13. rewrite Hk', Hk in H13.
  apply H13.
Qed.
Hint Resolve bind_state_sound : soundness.
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


Lemma extract_build_val_sound : forall v,
  gamma (extract_build_val (M:=AbstractState) (A:=isnat_parity) v) 
        (extract_build_val (M:=ConcreteState) v).
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

