Require Export Base.
Require Export Instances.Galois.
Require Import Classes.Functor.
Require Import Classes.Applicative.
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
Require Import Classes.SoundMonad.

(* Soundness of unit *)
Lemma gamma_unit_sound :
  gamma tt tt.
Proof. constructor.  Qed.
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
  intro. unfold gamma; simpl; unfold gamma_fun. eauto with soundness. 
Qed.
Hint Resolve gamma_fun_applied : soundness.

(* Soundness of monadic operations *)
Lemma fmap_maybe_sound {A A'} `{Galois A A'} : gamma fmap_maybe fmap_maybe.
Proof.
  intros ???. unfold fmap_maybe. intros ???. destruct a0, b0; eauto with
    soundness.
Qed.
Hint Resolve fmap_maybe_sound : soundness.

Lemma pure_maybe_sound {A A'} `{Galois A A'} : gamma Just Just.
Proof.
  eauto with soundness.
Qed.
Hint Resolve pure_maybe_sound : soundness.

Lemma bind_maybe_sound {A A' : Type} `{Galois A A'} : 
  gamma (bind_maybe (A:=A'))  bind_maybe.
Proof.
  intros f g Hfg x y Hxy. destruct f, g; eauto with soundness.
  inv Hfg.
Qed.
Hint Resolve bind_maybe_sound : soundness.

Lemma app_maybe_sound {A A'} `{Galois A A'} : gamma app_maybe app_maybe.
Proof. 
  intros f g Hfg x y Hxy. destruct f, g, x, y; simpl; eauto with soundness.
Qed.

Instance maybe_sound {A A'} `{Galois A A'} : SoundMonads Maybe Maybe :=
{
  fmap_sound := fmap_maybe_sound;
  pure_sound := pure_maybe_sound;
  app_sound := app_maybe_sound;
  bind_sound := bind_maybe_sound;
}. 

Lemma fmap_abstract_maybe_sound {A A'} `{Galois A A'} : 
  gamma fmap_abstract_maybe fmap_maybe.
Proof.
  intros ???. unfold fmap_abstract_maybe, fmap_maybe. intros ???. 
  destruct a0, b0; eauto with soundness.
Qed.
Hint Resolve fmap_maybe_sound : soundness.

Lemma pure_abstract_maybe_sound {A A'} `{Galois A A'} :
  gamma (JustA (A:=A')) (Just).
Proof.
  intros f g Hfg. apply Hfg.
Qed.

Lemma app_abstract_maybe_sound {A A'} `{Galois A A'} :
  gamma app_abstract_maybe app_maybe.
Proof.
  intros f g Hfg x y Hxy. destruct f, x, g, y; eauto with soundness;
  apply Hfg; apply Hxy.
Qed.

Lemma bind_abstract_maybe_sound {A A'} `{Galois A A'} :
  gamma (bind_maybeA (A:=A')) bind_maybe.
Proof.
  intros f g Hfg x y Hxy. destruct f, g; eauto with soundness.
  inv Hfg. simpl in *. apply Hxy in Hfg. destruct (x a), (y a0);
  eauto with soundness. simpl. destruct (x a); reflexivity.
Qed.

Instance maybeA_sound {A A'} `{Galois A A'} : 
  SoundMonads Maybe AbstractMaybe :=
{
  fmap_sound := fmap_abstract_maybe_sound;
  pure_sound := pure_abstract_maybe_sound;
  app_sound := app_abstract_maybe_sound;
  bind_sound := bind_abstract_maybe_sound;
}.

Instance state_sound {S S' A A'} `{Galois S S', Galois A A'} 
  : SoundMonads (State store) (State abstract_store).
Proof. split; intros f g Hfg x y Hxy.
- intros s t Hst. simpl.
  unfold fmap_state. apply Hxy in Hst. repeat destr. simpl in *.
  destruct Hst as [Ha Ha']. split.
  apply Hfg. apply Ha. apply Ha'.
- simpl. split. apply Hfg. apply Hxy.
- simpl. unfold app_state, gamma_pairs.
  intros s t Hst. apply Hfg in Hst. destruct (f s) as [f' s'] eqn:Hfs.
  destruct (g t) as [g' t'] eqn:Hgt. destruct Hst as [Hfg' Hst'].
  apply Hxy in Hst'.
  destruct (x s') as [x' s''] eqn:Hxs. destruct (y t') as [y' t''] eqn:Hyt. 
  destruct Hst' as [Hxy' Hst'']. split. apply Hfg'. apply Hxy'. apply Hst''.
- intros s t Hst. simpl. unfold bind_state. apply Hfg in Hst.
  destr; destr. destruct Hst. apply Hxy; assumption. 
Defined.

Instance composed_monad_sound {S S' A A'} `{Galois S S', Galois A A'} : 
  SoundMonads ConcreteState AbstractState.
Proof. 
  pose proof maybeA_sound. destruct H3. split.
  - simpl in *. unfold fmap_maybeAT, fmap_maybeT.
    intros ???. intros ???. simpl. unfold fmap_stateT. intros ???.
    simpl. apply bind_maybe_sound. auto. intros ???. destruct a2, b2.
    apply gamma_fun_apply. apply pure_maybe_sound.
    destruct H6. split; eauto with soundness.
  - simpl in *. unfold pure_maybeAT, pure_maybeT. intros ???.
    apply gamma_fun_apply; auto. simpl. unfold pure_stateT.
    intros ??????. apply pure_maybe_sound. split; auto.
  - simpl in *. unfold app_maybeAT, app_maybeT. simpl.
    intros ??????. unfold bind_stateT. intros ???.
    apply gamma_fun_apply; eauto with soundness. 
    apply gamma_fun_apply; eauto with soundness. 
    unfold bind_maybe.
Admitted.
Transparent composed_monad_sound.

Section stateT_sound.
  Context {S S' A A' B B'} `{Galois S S', Galois A A', Galois B B'}.
  Context {M M' : Type → Type} `{Galois (M B) (M' B'), Monad M, Monad M'}.
  Context `{Galois (M A) (M A')}.
  Context `{Galois (M (B*S)) (M' (B'*S'))}.
  Context `{SoundMonads M M'}.

  Lemma foobar : ∀ n, n. Admitted.
  Lemma fmap_stateT_sound : ∀ f' f k' k,
    gamma (@fmap_stateT M' _ _ _ S' A' B' f' k') (
           @fmap_stateT M _ _ _ S A B f k).
  Proof.
    intros. unfold fmap_stateT. 
  Admitted.
  (*
  Preorder.statet_preorder:
  ∀ (S A : Type) (M : Type → Type),
    PreorderedSet (M (A * S)%type) → PreorderedSet (StateT S M A)
    *)

End stateT_sound.

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

Lemma lift_maybeAT_sound {A A'} `{Galois A A'} : 
  gamma (lift_maybeAT (A:=A')) (lift_maybeT (A:=A)).
Proof.
  unfold lift_maybeAT, lift_maybeT.
  intros ??????. simpl. apply H1 in H2. 
  destruct (a a0), (b b0); eauto with soundness.
  destruct p, p0. apply H2. inv H2.
Qed.
Hint Resolve lift_maybeAT_sound : soundness.

Lemma lift_stateT_sound {A A' S S'} `{Galois S S', Galois A A'} :
  gamma lift_stateT lift_stateT.
Proof.
Admitted.
Hint Resolve lift_stateT_sound : soundness.

(* Monadic versions of parity operations *)
Hint Unfold gamma : soundness.
Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof.
  unfold ensure_par, ensure_nat. intros a c H. destruct a eqn:?, c eqn:?;
    try contradiction.
  - apply gamma_fun_apply. apply lift_maybeAT_sound. 
    apply gamma_fun_apply. simpl. unfold pure_stateT. intros ??????. 
    simpl. split; assumption. assumption.
  - apply gamma_fun_apply. apply lift_stateT_sound.
    eauto with soundness.
  - simpl. unfold lift_stateT, fmap_stateT. intros s t Hst. simpl. auto.
  - simpl. unfold lift_stateT, fmap_stateT, pure_stateT.
    simpl. intros s t Hst. simpl. auto.
  - apply gamma_fun_apply. apply lift_stateT_sound. auto.
Qed.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound :  forall n,
  gamma (extract_parM n) (extract_natM n). 
Proof. 
  intros. unfold extract_parM, extract_natM.  apply gamma_fun_apply.
  apply lift_maybeAT_sound. apply gamma_fun_apply; eauto with soundness.
  simpl. unfold pure_stateT. intros ???. intros ???. apply gamma_fun_apply.
  simpl. intros ???. auto. split; auto.
Qed.
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound : 
  gamma pplusM plusM.
Proof. 
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold pplusM, plusM. apply gamma_fun_apply. 
  apply lift_maybeAT_sound.
  eauto with soundness. apply gamma_fun_apply; eauto with soundness.
  simpl. unfold pure_stateT. intros ??????. apply gamma_fun_apply.
  eauto with soundness. split; auto.
Qed.
(*  repeat constructor; simpl; eauto with soundness.

  destruct H2. apply H2. destruct H1. apply H1.
Qed.*)
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound :
  gamma pmultM multM.
Proof.
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold pmultM, multM. apply gamma_fun_apply. apply lift_maybeAT_sound.
  apply gamma_fun_apply. simpl. unfold pure_stateT. intros ??????.
  apply gamma_fun_apply; auto with soundness. split; auto.
  eauto with soundness.
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound :
  gamma peqM eqbM.
Proof.
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold peqM, eqbM. apply gamma_fun_apply. apply lift_maybeAT_sound.
  apply gamma_fun_apply. simpl. unfold pure_stateT. intros ??????.
  apply gamma_fun_apply. simpl. eauto with soundness. split; auto.
  eauto with soundness.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound :
  gamma pleM lebM.
Proof.
  simpl; unfold gamma_fun; intros.
  simpl; unfold gamma_fun; intros.
  unfold pleM, lebM. apply gamma_fun_apply. apply lift_maybeAT_sound.
  apply gamma_fun_apply. simpl. unfold pure_stateT. intros ??????.
  apply gamma_fun_apply. simpl. eauto with soundness. split; auto.
  reflexivity. 
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound :
  gamma build_parity build_natural.
Proof.
  intros ???. 
  unfold build_parity, build_natural. apply gamma_fun_apply.
  apply lift_maybeAT_sound. apply gamma_fun_apply. simpl; unfold pure_stateT.
  intros ??????. apply gamma_fun_apply. simpl. eauto with soundness. split;
  auto. auto.
Qed.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on intervals *)
Require Import Omega.
Lemma iplusM_sound :
  gamma iplusM plusM.
Proof. 
  intros ???. intros ???. unfold iplusM, plusM. apply gamma_fun_apply;
  eauto with soundness. apply gamma_fun_apply. simpl. unfold pure_stateT.
  intros ??????. apply gamma_fun_apply; eauto with soundness. split; auto.
  simpl. unfold gamma_interval. split.
  - rewrite interval_min_plus. destruct H0, H. simpl in *. omega.
  - rewrite interval_max_plus. destruct H0, H. simpl in *. omega.
Qed.
Hint Resolve iplusM_sound : soundness.

Lemma imultM_sound :
  gamma imultM multM.
Proof.
  intros ???. intros ???. unfold imultM, multM. apply gamma_fun_apply;
  eauto with soundness. apply gamma_fun_apply; eauto with soundness.
  simpl. unfold pure_stateT. intros ??????. apply gamma_fun_apply; eauto
    with soundness. split; auto.
  simpl. unfold gamma_interval. split.
  - rewrite interval_min_mult. destruct H, H0; simpl in *. 
    apply Coq.Arith.Mult.mult_le_compat; auto.
  - rewrite interval_max_mult. destruct H, H0; simpl in *.
    apply Coq.Arith.Mult.mult_le_compat; auto.
Qed.
Hint Resolve imultM_sound.

Lemma ileqb_sound :
  gamma ileM lebM.
Proof.
  intros ???. intros ???. unfold ileM, lebM. apply gamma_fun_apply; eauto with
    soundness.
  apply gamma_fun_apply; eauto with soundness. simpl. unfold pure_stateT.
  intros ??????. apply gamma_fun_apply; eauto with soundness. split; auto.
  unfold ileqb. destruct H, H0. simpl in *. unfold Galois.gamma_bool.
  destruct (max a <? min a0) eqn:Hcompa, (b <=? b0) eqn:Hcompb.
  reflexivity. rewrite leb_iff_conv in Hcompb. assert (min a0 <= max a). 
  eapply le_trans. apply H0. 
Admitted.
Hint Resolve ileqb_sound : soundness.

Lemma ieqM_sound : gamma ieqM eqbM.
Proof.
  intros ???. intros ???. unfold ieqM, eqbM.
  apply gamma_fun_apply; eauto with soundness. 
Admitted.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound :
  gamma build_interval build_natural.
Proof.
  intros ???. unfold build_interval, build_natural.
  apply gamma_fun_apply; eauto with soundness. 
  apply gamma_fun_apply; eauto with soundness. simpl. unfold pure_stateT.
  intros ??????. apply gamma_fun_apply; eauto with soundness.
  split; auto.
Qed.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound : forall n,
  gamma (extract_interval n) (extract_natM n).
Proof.
  intros ?. unfold extract_interval, extract_natM.
  apply gamma_fun_apply; eauto with soundness.
  simpl. unfold pure_stateT. intros ???. simpl.
  split; auto.
  unfold gamma_interval. rewrite interval_min_refl, interval_max_refl. 
  split; apply preorder_refl.
Qed.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound : gamma ensure_interval ensure_nat.
Proof.
  intros ???. unfold ensure_interval, ensure_nat.
  destruct a, b; try contradiction.
  - simpl. unfold lift_stateT. intros ???. simpl. auto.
  - apply gamma_fun_apply; eauto with soundness. apply lift_stateT_sound.
  - apply gamma_fun_apply; eauto with soundness. 
  - simpl. unfold lift_stateT. intros ???. simpl. auto.
  - simpl. unfold lift_stateT. intros ???. simpl. auto.
Qed.
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
  destruct a, b; eauto with soundness; try contradiction;
  try apply gamma_fun_apply; eauto with soundness. apply lift_stateT_sound.
  simpl. unfold pure_stateT. intros ???. apply gamma_fun_apply; eauto with
    soundness. split; auto. apply lift_stateT_sound. apply lift_stateT_sound.
  simpl. unfold lift_stateT. intros ???. simpl. auto.
Qed.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound :
  gamma neg_abM negbM.
Proof.
  intros ???. unfold neg_abM, negbM. apply gamma_fun_apply; eauto with
    soundness.
  apply gamma_fun_apply; eauto with soundness.
  simpl. unfold pure_stateT. intros ??????. simpl. split; auto.
  destruct a, b; eauto with soundness.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound :
  gamma and_abM andbM.
Proof.
  intros ??????. unfold and_abM, andbM. apply gamma_fun_apply;
  eauto with soundness. apply gamma_fun_apply. simpl.
  intros ??????. unfold pure_stateT. simpl. split; auto.
  destruct a, b, a0, b0; eauto with soundness.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound: forall b,
  gamma (extract_abM b) (extract_boolean b).
Proof. 
  intro b. unfold extract_abM, extract_boolean. apply gamma_fun_apply;
  eauto with soundness. apply gamma_fun_apply; eauto with soundness. 
  simpl. intros ??????. unfold pure_stateT. split; auto.
  destruct b; eauto with soundness.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound :
  gamma build_abool build_boolean.
Proof.
  intros ???. unfold build_abool, build_boolean.
  apply gamma_fun_apply; eauto with soundness.
  apply gamma_fun_apply; eauto with soundness.
  simpl. unfold pure_stateT; intros ??????; simpl. split; auto.
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
  - intros ???. apply gamma_fun_apply; eauto with soundness. 
    (* apply bindM_sound, apply extract sound, build sound *)
    admit.
  - (* as above *)
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
  intros ?????????.
  destruct b. 
  - (* true *)
    destruct a. 
    + apply H0. 
    + unfold gamma in H; simpl in H. contradiction.
    + unfold eval_if_abstract, eval_if. apply widen with (f:=a0).
      apply join_upper_bound_left. apply H0.
    + unfold gamma in H; simpl in H. contradiction.
  - destruct a; simpl.
    + unfold gamma in H; simpl in H; contradiction.
    + apply H1.
    + eapply widen with (f:=a1). apply join_abstract_store_right. auto.
    + unfold gamma in H; simpl in H; contradiction.
Qed.
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

