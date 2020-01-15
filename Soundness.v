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

Hint Extern 10 (gamma _ _) => gamma_destruct : soundness.

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
Proof. 
  eauto with soundness.
Qed.
Hint Resolve gamma_fun_apply : soundness.
Arguments gamma_fun_apply [A A' B B'] {H H0} f f' x x'.

Lemma gamma_fun_applied {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') :
      (forall x x', gamma x' x -> gamma (f' x') (f x)) ->
        gamma f' f.
Proof. 
  eauto with soundness.
Qed.
Arguments gamma_fun_applied [A A' B B' H H0] f f'.
(*Hint Resolve gamma_fun_applied : soundness.*)

(* Soundness of monadic operations *)
Lemma fmap_maybe_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (fmap (F:=Maybe) (A:=A') (B:=B')) 
        (fmap (F:=Maybe) (A:=A) (B:=B)).
Proof.
  repeat constructor. 
  eauto with soundness.
Qed.
Hint Resolve fmap_maybe_sound : soundness.

Lemma pure_maybe_sound : ∀ (A A' : Type) `{Galois A A'},
  gamma (pure (F:=Maybe) (A:=A')) pure.
Proof.
  eauto with soundness.
Qed.
Hint Resolve pure_maybe_sound : soundness.

Lemma bind_maybe_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (bindM (M:=Maybe) (A:=A')) 
        bindM.
Proof.
  repeat constructor. intros.
  destruct a', a; eauto with soundness.
  simpl; eauto with soundness.
Qed.
Hint Resolve bind_maybe_sound : soundness.

Lemma app_maybe_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (app (F:=Maybe) (A:=A') (B:=B')) app.
Proof. 
  repeat constructor.
  intros. destruct a, a', a0, a'0; eauto with soundness.
Qed.

Instance maybe_sound {A A' B B'} `{Galois A A', Galois B B'} : SoundMonad Maybe Maybe :=
{
  fmap_sound := fmap_maybe_sound;
  pure_sound := pure_maybe_sound;
  app_sound  := app_maybe_sound;
  bind_sound := bind_maybe_sound;
}. 

Lemma fmap_abstract_maybe_sound (A A' B B' : Type) `{Galois A A', Galois B B'} : 
  gamma (fmap (F:=AbstractMaybe) (A:=A') (B:=B')) fmap.
Proof.
  repeat constructor. intros. destruct a0, a'0; eauto with soundness.
Qed.
Hint Resolve fmap_maybe_sound : soundness.

Lemma pure_abstract_maybe_sound (A A' : Type) `{Galois A A'} :
  gamma (pure (F:=AbstractMaybe)) pure.
Proof.
  eauto with soundness.
Qed.

Lemma app_abstract_maybe_sound (A A' B B' : Type) `{Galois A A', Galois B B'} :
  gamma (app (F:=AbstractMaybe) (A:=A') (B:=B')) app.
Proof.
  repeat constructor. 
  intros. destruct a, a0; inv H1; inv H2; eauto with soundness.
Qed.

Lemma bind_abstract_maybe_sound (A A' B B' : Type) `{Galois A A', Galois B B'} :
  gamma (bindM (M:=AbstractMaybe) (A:=A')) bindM.
Proof.
  repeat constructor. intros.
  destruct a, a'; simpl; eauto with soundness.
  gamma_destruct. apply H3 in H5. destruct (a0 a); eauto with soundness.
  destruct (a'0 a); constructor.
Qed.

Instance maybeA_sound {A A' B B'} `{Galois A A', Galois B B'} : 
  SoundMonad Maybe AbstractMaybe :=
{
  fmap_sound := fmap_abstract_maybe_sound;
  pure_sound := pure_abstract_maybe_sound;
  app_sound  := app_abstract_maybe_sound;
  bind_sound := bind_abstract_maybe_sound;
}.
Hint Resolve fmap_abstract_maybe_sound
             pure_abstract_maybe_sound
             app_abstract_maybe_sound
             bind_abstract_maybe_sound : soundness.

Lemma fmap_state_sound {S S' : Type} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'}, 
  gamma (Galois:=GFun) 
  (B:=((A' → B') → State S' A' → State S' B'))
        (fmap_state (A:=A') (B:=B') (S:=S'))
        fmap_state.
Proof.
  unfold fmap_state. repeat constructor.
  - repeat destr. simpl. gamma_destruct. apply H5 in H4.
    rewrite Heqp in H4. rewrite Heqp0 in H4. 
    eauto with soundness.
  - repeat destr. simpl. gamma_destruct. apply H5 in H4.
    rewrite Heqp in H4; clear Heqp.
    rewrite Heqp0 in H4; clear Heqp0.
    eauto with soundness.
Qed.

Lemma pure_state_sound {S S' : Type} `{Galois S S'} : ∀ (A A' : Type) 
  `{Galois A A'},
  gamma 
    (pure_state (A:=A') (S:=S')) 
    pure_state.
Proof.
  eauto with soundness. 
Qed.

Lemma app_state_sound {S S'} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'},
  gamma
    (app_state (S:=S') (A:=A') (B:=B'))
    app_state.
Proof. 
  unfold app_state. repeat constructor.
  - gamma_destruct. apply H3 in H4.
    destruct (a a1), (a' a'1).
    gamma_destruct. apply H5 in H6. simpl in H6. 
    destruct (a0 s), (a'0 s0). eauto with soundness.
  - gamma_destruct. apply H3 in H4. destruct (a' a'1), (a a1).
    gamma_destruct. apply H5 in H6; simpl in H6.
    destruct (a'0 s), (a0 s0). 
    eauto with soundness.
Qed.

Lemma bind_state_sound {S S'} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'},
  gamma
    (bind_state (S:=S') (A:=A') (B:=B'))
    bind_state.
Proof. 
  unfold bind_state. repeat constructor.
  - gamma_destruct. apply H3 in H4. destruct (a a1), (a' a'1).
    gamma_destruct. apply H5 in H2.
    gamma_destruct. apply H4 in H6. inv H6.
    apply H2.
  - gamma_destruct. apply H3 in H4. destruct (a a1), (a' a'1).
    gamma_destruct. apply H5 in H2.
    gamma_destruct. apply H4 in H6. inv H6.
    eauto with soundness.
Qed.

Instance state_sound {S S' : Type} `{HS : Galois S S'} 
  : SoundMonad (State S) (State S') :=
{
  fmap_sound := @fmap_state_sound S S' HS;
  pure_sound := @pure_state_sound S S' HS;
  app_sound  := @app_state_sound S S' HS;
  bind_sound := @bind_state_sound S S' HS;
}.
Hint Resolve fmap_state_sound pure_state_sound app_state_sound 
             bind_state_sound : soundness.

Lemma fmap_stateT_sound {M M' : Type → Type}
   `{SoundMonad M M'} {S S' : Type} 
  `{Galois S  S'} : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (fmap_stateT (A:=A') (B:=B') (S:=S') (M:=M'))
         fmap_stateT.
Proof.
  intros. unfold fmap_stateT. constructor. intros. constructor.
  intros. constructor. intros. repeat eapply gamma_fun_apply; eauto with
    soundness.
  constructor; intros. destruct a2, a'2. 
  repeat eapply gamma_fun_apply; eauto with soundness.
Qed.

Lemma pure_stateT_sound {M M' : Type → Type} `{SoundMonad M M'} {S S' : Type}
  `{Galois S S'} : ∀ (A A' : Type) `{Galois A A'},
  gamma (pure_stateT (A:=A') (S:=S') (M:=M')) pure_stateT.
Proof.
  intros. unfold pure_stateT. repeat constructor. intros. repeat eapply
  gamma_fun_apply; eauto with soundness.
Qed.

Lemma app_stateT_sound {M M' : Type → Type} `{SoundMonad M M'} {S S' : Type}
  `{Galois S S'} : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (app_stateT (A:=A') (B:=B') (S:=S') (M:=M')) app_stateT.
Proof.
  intros. unfold app_stateT. repeat constructor; intros.
  repeat eapply gamma_fun_apply; eauto with soundness.
  constructor; intros. destruct a'2, a2. repeat eapply gamma_fun_apply; eauto
  with soundness. constructor; intros. destruct a'2, a2. repeat eapply
  gamma_fun_apply; eauto with soundness.
Qed.

Lemma bind_stateT_sound {M M' : Type → Type} `{SoundMonad M M'} {S S' : Type}
  `{Galois S S'} : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (bind_stateT (A:=A') (B:=B') (S:=S') (M:=M')) bind_stateT.
Proof.
  intros. unfold bind_stateT. repeat constructor; intros. repeat eapply
  gamma_fun_apply; eauto with soundness. constructor; intros.
  destruct a'2, a2. repeat eapply gamma_fun_apply; eauto with soundness.
Qed.

Instance stateT_sound {M M'} `{SoundMonad M M'} {S S' : Type} `{Galois S S'} : 
  SoundMonad (StateT S M) (StateT S' M') :=
  {
    fmap_sound := fmap_stateT_sound;
    pure_sound := pure_stateT_sound;
    app_sound := app_stateT_sound;
    bind_sound := bind_stateT_sound;
  }.

Section concrete_state_maybe_sound.
  Global Instance sound_stateT_store_maybe :
    SoundMonad (StateT store Maybe) (StateT abstract_store Maybe).
  Proof.
    constructor.
    - (* fmap_sound *)
      intros. simpl. unfold fmap_stateT. repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
      constructor. intros. destruct a2, a'2. 
      repeat eapply gamma_fun_apply; eauto with soundness.
    - (* pure_sound *)
      intros. simpl. unfold pure_stateT. constructor.
      intros. constructor. intros. constructor. constructor.
      repeat eapply gamma_fun_apply; eauto with soundness.
      repeat eapply gamma_fun_apply; eauto with soundness.
    - (* app_sound *)
      intros. simpl. unfold app_stateT. repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness. simpl.
      constructor; intros. destruct a2, a'2. 
      repeat eapply gamma_fun_apply; eauto with soundness. 
      constructor; intros. destruct a3, a'2. 
      repeat eapply gamma_fun_apply; eauto with soundness.
    - (* bind_sound *)
      intros. simpl. unfold bind_stateT. repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness. 
      constructor. intros. destruct a2, a'2. eauto with soundness.
  Qed.
End concrete_state_maybe_sound.

Instance states_sound : SoundMonad ConcreteState AbstractState.
Proof.
  constructor.
  - intros. simpl. unfold fmap_maybeAT, fmap_maybeT. simpl. unfold fmap_stateT.
    simpl. repeat constructor. intros. 
    repeat eapply gamma_fun_apply; eauto with soundness. constructor.
    intros. destruct a'2, a2. inv H2. repeat eapply gamma_fun_apply; eauto with
      soundness.
  - intros. simpl. unfold pure_maybeAT, pure_maybeT. simpl. unfold pure_stateT.
    repeat constructor; eauto with soundness.
  - intros. simpl. unfold app_maybeAT, app_maybeT. simpl. unfold pure_stateT,
    bind_stateT. repeat constructor; intros. 
    repeat eapply gamma_fun_apply; eauto with soundness.
    repeat constructor; intros. destruct a'2, a2. inv H2. simpl in *.
    eapply gamma_fun_apply; auto.
    destruct a3, m.
    + repeat constructor; intros. repeat eapply gamma_fun_apply. 1-3: eauto with
      soundness. constructor. intros. destruct a'3, a3. inv H7; simpl in *.
      destruct a5, m; repeat eapply gamma_fun_apply; eauto with soundness.
    + inv H3.
    + repeat constructor. intros. repeat eapply gamma_fun_apply. 1-3: eauto with
      soundness. constructor. intros. destruct a'3, a3. inv H7; simpl in *. 
      destruct a5, m; repeat eapply gamma_fun_apply; eauto with soundness.
    + admit. 
    + constructor; intros. admit.
    + eauto with soundness.
  - intros. simpl. unfold bind_maybeAT, bind_maybeT. repeat constructor;
    intros. simpl. unfold bind_stateT. repeat eapply gamma_fun_apply; 
    eauto with soundness. constructor. intros. destruct a'2, a2.
    intros. inv H2. simpl in *. destruct a3, m; repeat eapply gamma_fun_apply;
    auto with soundness. simpl. 
Admitted.

(* Soundness of parity operations *)

Lemma gamma_par_extract_n_n : forall n,
  gamma (extract_par n) n.
Proof.
  intros. autounfold with soundness. 
  destruct (Nat.even n) eqn:Hpar. 
  - rewrite Nat.even_spec in Hpar. eauto with soundness.
  - pose proof Nat.negb_even. 
    constructor.
    rewrite <- Nat.odd_spec. rewrite <- Nat.negb_even, Bool.negb_true_iff.
    assumption.
Qed.
Hint Resolve gamma_par_extract_n_n : soundness.

Lemma parity_plus_sound :
  gamma parity_plus plus.
Proof.
  autounfold with soundness. repeat constructor. intros.
  destruct a', a'0; eauto with soundness.
Qed.
Hint Resolve parity_plus_sound : soundness.

Lemma parity_mult_sound :
  gamma parity_mult mult.
Proof. 
  autounfold with soundness. repeat constructor. intros.
  destruct a, a0; eauto with soundness.
Qed.
Hint Resolve parity_mult_sound : soundness.

Hint Rewrite Nat.eqb_eq : soundness.
Lemma parity_eq_sound :
  gamma parity_eq Nat.eqb. 
Proof. 
  unfold parity_eq. repeat constructor. intros.
  destruct a, a0; eauto with soundness; inv H; inv H0.
  - constructor. rewrite Nat.eqb_neq.
    unfold not. intros. subst. eauto using Nat.Even_Odd_False.
  - constructor. rewrite Nat.eqb_neq. unfold not.
    intros. subst. eauto using Nat.Even_Odd_False.
Qed.
Hint Resolve parity_eq_sound : soundness.

Lemma extract_par_sound : forall n,
  gamma (VParity (extract_par n)) (VNat n).
Proof. 
  simple_solve. rewrite Nat.even_spec in Heqb. eauto with soundness.
  constructor. constructor. 
  rewrite <- Nat.odd_spec. unfold Nat.odd. rewrite Heqb.
  reflexivity.
Qed.

Lemma lift_maybeAT_sound {A A'} `{Galois A A'} {M M'} `{SoundMonad M M'} : 
  gamma (lift_maybeAT (M:=M') (A:=A')) (lift_maybeT (A:=A)).
Proof.
  unfold lift_maybeAT, lift_maybeT. 
  repeat constructor. intros.
  simpl. 
  repeat eapply gamma_fun_apply; eauto with soundness.
  destruct H6. apply fmap_sound.
Qed.
Hint Resolve lift_maybeAT_sound : soundness.

(* Monadic versions of parity operations *)
Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof.
  unfold ensure_par, ensure_nat. constructor. 
  intros. destruct a, b; inv H. 
  - simpl. repeat eapply gamma_fun_apply. 
Qed.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound : forall n,
  gamma (extract_parM n) (extract_natM n). 
Proof. 
  intros. unfold extract_parM, extract_natM.  
  repeat eapply gamma_fun_apply; eauto with soundness.
  simpl. 
Admitted. 
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound : 
  gamma pplusM plusM.
Proof. 
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound :
  gamma pmultM multM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound :
  gamma peqM eqbM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound :
  gamma pleM lebM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound :
  gamma build_parity build_natural.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on intervals *)
Require Import Omega.
Lemma iplusM_sound :
  gamma iplusM plusM.
Proof. 
  repeat constructor; eauto with soundness.
  - rewrite interval_min_plus. destruct H0, H. simpl in *. omega.
  - rewrite interval_max_plus. destruct H0, H. simpl in *. omega.
Qed.
Hint Resolve iplusM_sound : soundness.

Lemma imultM_sound :
  gamma imultM multM.
Proof.
  repeat constructor; eauto with soundness.
  - rewrite interval_min_mult. destruct H, H0; simpl in *. 
    apply Coq.Arith.Mult.mult_le_compat; auto.
  - rewrite interval_max_mult. destruct H, H0; simpl in *.
    apply Coq.Arith.Mult.mult_le_compat; auto.
Qed.
Hint Resolve imultM_sound.

Lemma ileqb_sound :
  gamma ileM lebM.
Proof.
  repeat constructor; eauto with soundness.
  unfold ileqb. destruct H, H0. simpl in *. 
  destruct (max i <? min i0) eqn:Hcompa, (n <=? n0) eqn:Hcompb.
  constructor; reflexivity. 
  rewrite leb_iff_conv in Hcompb. assert (min i0 <= max i). 
  eapply le_trans. apply H0. 
Admitted.
Hint Resolve ileqb_sound : soundness.

Lemma ieqM_sound : gamma ieqM eqbM.
Proof.
  repeat constructor; eauto with soundness.
  repeat eapply gamma_fun_apply; eauto with soundness. 
Admitted.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound :
  gamma build_interval build_natural.
Proof.
  repeat constructor; simpl; destruct H; eauto with soundness.
Qed.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound : forall n,
  gamma (extract_interval n) (extract_natM n).
Proof.
  repeat constructor; unfold min, max; simpl; try rewrite Nat.leb_refl; 
    eauto with soundness.
Qed.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound : gamma ensure_interval ensure_nat.
Proof.
  repeat constructor; eauto with soundness.
  intros ???. unfold ensure_interval, ensure_nat.
  destruct a, b; try contradiction; eauto with soundness.
  repeat eapply gamma_fun_apply; eauto with soundness.
  simpl. 
Admitted.
Hint Resolve ensure_interval_sound : soundness.

(* Soundness of operations on booleans *)

Lemma ab_and_sound :
  gamma and_ab andb.
Proof. 
  unfold and_ab, andb.
  repeat constructor.
  intros ???. 
  destruct a, a0, b, b0; eauto with soundness.
Qed.
Hint Resolve ab_and_sound : soundness.

Lemma ab_or_sound :
  gamma or_ab orb.
Proof. 
  repeat constructor.
  intros ???. destruct a, a0, b, b0; auto with soundness.
Qed.
Hint Resolve ab_or_sound : soundness.

Lemma ab_neg_sound :
  gamma neg_ab negb.
Proof. 
  repeat constructor.
  destruct a, b; eauto with soundness.
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
  repeat constructor. 
  intros ???. unfold ensure_abool, ensure_bool. 
  destruct a, b; eauto with soundness. 
  repeat eapply gamma_fun_apply; eauto with soundness.
  simpl. 
Admitted.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound :
  gamma neg_abM negbM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound :
  gamma and_abM andbM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound: forall b,
  gamma (extract_abM b) (extract_boolean b).
Proof. 
  repeat constructor; eauto with soundness.
  destruct b; eauto with soundness.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound :
  gamma build_abool build_boolean.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_boolean_sound : soundness.

(* Soundness of applied functions *)

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
  unfold t_update. repeat constructor; eauto with soundness.
  intros x'. destruct (beq_string x x'); eauto with soundness.
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

Lemma extract_build_val_sound : forall v,
  gamma (extract_build_val (M:=AbstractState) (A:=isnat_parity) v) 
        (extract_build_val (M:=ConcreteState) v).
Proof.
  destruct v; repeat constructor; eauto with soundness. destruct b; auto with
    soundness.
Qed.
Hint Resolve extract_build_val_sound : soundness.

Theorem eval_expr_sound : forall a,
  gamma (shared_eval_expr (M:=AbstractState) (A:=isnat_parity) a) 
        (shared_eval_expr (M:=ConcreteState) a).
Proof.
  intros. induction a; repeat constructor; simpl.
  - eauto with soundness.
  - eauto with soundness.
  - eauto with soundness.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. intros. admit.
  - eauto with soundness. admit.
  - eauto with soundness. 
Admitted.
Hint Resolve eval_expr_sound : soundness.

Lemma sound_if_op : 
  gamma (eval_if_abstract)
  (eval_if).
Proof.
  constructor. intros. constructor. intros. constructor. intros.
  destruct b. 
Admitted.

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
  induction c; simpl. 
  - eauto with soundness.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness.
Admitted.

