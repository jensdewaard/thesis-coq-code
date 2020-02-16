Require Export Base.
Require Import Omega.
Require Export Instances.Galois.
Require Import Classes.Galois.
Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
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
Require Import Instances.Preorder.
Require Import Instances.Store.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.Interval.
Require Import Types.Stores.
Require Import Classes.SoundMonad.
Require Import Types.Maybe.
Require Import Types.State.

Hint Extern 0 (gamma _ _) => progress gamma_destruct : soundness.

Axiom gamma_pure_none : ∀ {M M' : Type → Type} `{Monad M, Monad M'} {A A' :
  Type}  `{Galois (M A) (M' (Maybe A'))} (c : M A), gamma (returnM (M:=M') None) c.
Hint Resolve gamma_pure_none : soundness.

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
Hint Extern 3 (gamma (?f ?x) (?g ?y)) => apply gamma_fun_apply : soundness.

Lemma gamma_fun_applied {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') :
      (forall x x', gamma x' x -> gamma (f' x') (f x)) ->
        gamma f' f.
Proof. 
  eauto with soundness.
Qed.
(*Hint Resolve gamma_fun_applied : soundness.*)

(* Soundness of monadic operations *)
Lemma just_sound : ∀ (A A' : Type) `{A_galois : Galois A A'},
  gamma (Just (A:=A')) (Just (A:=A)).
Proof.
  eauto with soundness.
Qed.

Lemma bind_maybe_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (bindM (M:=Maybe) (A:=A') (B:=B')) 
        bindM.
Proof.
  unfold bindM; simpl.
  repeat constructor. intros.
  destruct a', a; eauto with soundness.
Qed.
Hint Resolve bind_maybe_sound : soundness.

Instance maybe_sound : SoundMonad Maybe Maybe :=
{
  return_sound := just_sound;
  bind_sound := bind_maybe_sound;
}.

Lemma justA_sound : ∀ A A' `{A_galois : Galois A A'},
  gamma (JustA (A:=A')) Just.
Proof.
  eauto with soundness.
Qed.

Lemma bind_abstract_maybe_sound (A A' B B' : Type) `{Galois A A', Galois B B'} :
  gamma (bindM (M:=AbstractMaybe) (A:=A') (B:=B')) bindM.
Proof.
  unfold bindM; simpl.
  constructor; intros ma ma' Hma. constructor; intros mf mf' Hmf.
  destruct ma, ma' as [|a'|]; simpl; eauto with soundness.
  inversion Hma as [Ha |? |? |?? Ha];subst.
  inversion Hmf as [?? Hf]; subst.
  apply Hf in Ha. all: destruct (mf' a'); eauto with soundness.
Qed.

Instance abstract_maybe_sound : SoundMonad Maybe AbstractMaybe :=
{
  return_sound := justA_sound;
  bind_sound := bind_abstract_maybe_sound;
}.

Lemma bind_state_sound {S S'} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'},
  gamma
    (bind_state (S:=S') (A:=A') (B:=B'))
    bind_state.
Proof. 
  unfold bind_state. constructor; intros st st' Hst.
  constructor; intros f f' Hf. constructor; intros s s' Hs.
  inversion Hst as [?? Hgamma_st]; subst; clear Hst.
  apply Hgamma_st in Hs. destruct (st' s'), (st s).
  inversion Hs as [?? Ha Hs']; subst; clear Hs; simpl in *.
  repeat apply gamma_fun_apply; assumption.
Qed.
Hint Resolve bind_state_sound : soundness.

Section stateT.
  Context {M M' : Type → Type} `{SoundMonad M M'}.
  Context {S S' : Type} `{Galois S S'} `{!Inhabited S, !Inhabited S'}.

  Lemma return_stateT_sound : ∀ A A' `{A_galois : Galois A A'},
    gamma (return_stateT (S:=S') (M:=M') (A:=A')) (return_stateT (A:=A)).
  Proof.
    unfold return_stateT. eauto 10 using return_sound with soundness.
  Qed.

  Lemma bind_stateT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
    gamma (bind_stateT (A:=A') (B:=B') (S:=S') (M:=M')) bind_stateT.
  Proof.
    intros. unfold bind_stateT. repeat constructor; intros. repeat eapply
    gamma_fun_apply; eauto with soundness. constructor; intros p p' Hp.
    destruct p, p'. repeat eapply gamma_fun_apply; eauto with soundness.
  Qed.

  Global Instance stateT_sound : SoundMonad (StateT S M) (StateT S' M') :=
  {
    return_sound := return_stateT_sound;
    bind_sound := bind_stateT_sound;
  }.
End stateT.

Section maybeT.
  Context {M M' : Type → Type} `{SoundMonad M M'}.

  Lemma justT_sound : ∀ A A' `{Galois A A'},
    gamma (JustT (M:=M') (A:=A')) JustT.
  Proof. 
    unfold JustT, MaybeT. intros. constructor; intros.
    repeat eapply gamma_fun_apply; eauto with soundness. 
  Qed.

  Lemma bind_maybeT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
    gamma (bind_maybeT (A:=A') (B:=B') (M:=M')) bind_maybeT.
  Proof. 
    intros. unfold bind_maybeT, MaybeT, NoneT. repeat constructor; intros. 
    repeat eapply gamma_fun_apply; eauto with soundness.
  Qed.

  Global Instance maybeT_sound : SoundMonad (MaybeT M) (MaybeT M') :=
  {
    return_sound := justT_sound;
    bind_sound := bind_maybeT_sound;
  }.
End maybeT.

Section maybeAT.
  Context {M M' : Type → Type} `{SoundMonad M M'}.

  Lemma justAT_sound : ∀ A A' `{Galois A A'},
    gamma (JustAT (M:=M') (A:=A')) JustT.
  Proof.
    unfold JustAT, JustT, MaybeAT, MaybeT. eauto with soundness.
  Qed.

  Lemma bind_maybeAT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
    gamma (bind_maybeAT (A:=A') (B:=B') (M:=M')) bind_maybeT.
  Proof.
    intros. unfold bind_maybeAT, bind_maybeT. unfold MaybeT, MaybeAT.
    constructor; intros Ma Ma' HMa.
    constructor; intros f f' Hf'.
    repeat apply gamma_fun_apply; eauto with soundness. 
    constructor; intros m m' Hm. unfold NoneT.
    destruct m; inversion Hm; subst; eauto with soundness.
    - rewrite <- bind_id_right. eapply gamma_fun_apply.
      eauto with soundness.
      constructor; intros m m' Hm'. destruct m'; eauto with soundness.
    - admit.
  Admitted.

  Lemma lift_maybeAT_sound {A A'} `{Galois A A'} :
    gamma (lift_maybeAT (M:=M') (A:=A')) (lift_maybeT (A:=A)).
  Proof.
    unfold lift_maybeAT, lift_maybeT, MaybeAT, MaybeT, JustAT, JustT.
    repeat constructor. intros.
    repeat eapply gamma_fun_apply; eauto with soundness.
  Qed.

  Global Instance maybeAT_sound : SoundMonad (MaybeT M) (MaybeAT M') :=
  {
    return_sound := justAT_sound;
    bind_sound := bind_maybeAT_sound;
  }.
End maybeAT.

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

Lemma parity_plus_sound :
  gamma parity_plus plus.
Proof.
  autounfold with soundness. repeat constructor. intros.
  destruct a', a'0; eauto with soundness.
Qed.

Lemma parity_mult_sound :
  gamma parity_mult mult.
Proof. 
  autounfold with soundness. repeat constructor; intros.
  destruct a', a'0; gamma_destruct; try constructor; eauto with soundness.
Qed.

Hint Rewrite Nat.eqb_eq : soundness.
Lemma parity_eq_sound :
  gamma parity_eq Nat.eqb. 
Proof. 
  repeat constructor. intros. destruct a', a'0; simpl; try constructor.
  2: eauto with soundness. 3-8: eauto with soundness.
  gamma_destruct. assert (a ≠ a0). unfold not. intro; subst.
  apply (Nat.Even_Odd_False a0); auto. rewrite Nat.eqb_neq; auto.
  gamma_destruct. assert (a ≠ a0). unfold not. intro; subst.
  apply (Nat.Even_Odd_False a0); auto. rewrite Nat.eqb_neq; auto.
Qed.

Lemma extract_par_sound : forall n,
  gamma (extract_par n) n.
Proof. 
  intros. unfold extract_par. destruct (Nat.even n) eqn:Hpar; repeat constructor.
  rewrite <- Nat.even_spec; auto.
  rewrite <- Nat.odd_spec. unfold Nat.odd. rewrite Hpar. reflexivity.
Qed.

(* Monadic versions of parity operations *)
Lemma ensure_par_sound {M M'} `{SoundMonad M M'} 
  {M'_fail : MonadFail M'} {M_fail : MonadFail M} :
  gamma (ensure_par (M:=M')) ensure_nat.
Proof.
  constructor; intros a a' Hgamma. destruct a; inv Hgamma; subst; simpl; eauto
  with soundness.
Admitted.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound {M M'} `{SoundMonad M M'} : forall n,
  gamma (extract_parM n) (extract_natM n). 
Proof. 
  intros. unfold extract_parM, extract_natM. 
  repeat eapply gamma_fun_apply; eauto using extract_par_sound with soundness. 
Qed. 
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound {M M'} `{SoundMonad M M'} : 
  gamma pplusM plusM.
Proof. 
  unfold pplusM, plusM.
  repeat constructor; eauto using parity_plus_sound with soundness. 
Qed.
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound {M M'} `{SoundMonad M M'} :
  gamma pmultM multM.
Proof.
  unfold pmultM, multM.
  repeat constructor; eauto using parity_mult_sound with soundness. 
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound {M M'} `{SoundMonad M M'} :
  gamma peqM eqbM.
Proof.
  unfold peqM, eqbM.
  repeat constructor; eauto using parity_eq_sound with soundness.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound {M M'} `{SoundMonad M M'} :
  gamma pleM lebM.
Proof.
  unfold pleM, lebM.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound {M M'} `{SoundMonad M M'} :
  gamma build_parity build_natural.
Proof.
  unfold build_parity, build_natural.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on intervals *)
Lemma iplus_sound : gamma iplus plus.
Proof.
  repeat constructor. 
  - rewrite interval_min_plus. gamma_destruct. simpl in *. omega.
  - rewrite interval_max_plus. gamma_destruct. simpl in *. omega. 
Qed.

Lemma iplusM_sound {M M'} `{SoundMonad M M'} :
  gamma iplusM plusM.
Proof. 
  unfold iplusM, plusM.
  repeat constructor; intros. eauto using iplus_sound with soundness.
Qed.
Hint Resolve iplusM_sound : soundness.

Lemma imult_sound : gamma imult mult.
Proof.
  repeat constructor. 
  - rewrite interval_min_mult. gamma_destruct; simpl in *.
    apply Coq.Arith.Mult.mult_le_compat; auto.
  - rewrite interval_max_mult. gamma_destruct; simpl in *.
    apply Coq.Arith.Mult.mult_le_compat; auto.
Qed.

Lemma imultM_sound {M M'} `{SoundMonad M M'} :
  gamma imultM multM.
Proof.
  unfold imultM, multM.
  repeat constructor; intros. eauto using imult_sound with soundness.
Qed.
Hint Resolve imultM_sound : soundness.

Lemma ileqb_sound : gamma ileqb leb.
Proof.
  constructor; intros n i Hn; constructor; intros m j Hm.
  unfold ileqb. gamma_destruct; simpl in *.
  destruct (max i <? min j) eqn:Hij. 
  rewrite Nat.ltb_lt in Hij.
  assert (n <=? m = true) as Hnm. rewrite Nat.leb_le. omega. rewrite Hnm.
  auto with soundness. destruct (max j <? min i) eqn:Hji.
  rewrite Nat.ltb_lt in Hji. rewrite Nat.ltb_ge in Hij.
  assert (n <=? m = false) as Hnm. apply leb_correct_conv. omega.
  rewrite Hnm. constructor. reflexivity. constructor.
Qed.

Lemma ilebM_sound {M M'} `{SoundMonad M M'} :
  gamma ileM lebM.
Proof.
  unfold ileM, lebM.
  repeat constructor; intros. eauto using ileqb_sound with soundness.
Qed.
Hint Resolve ileqb_sound : soundness.

Lemma ieqb_sound : gamma ieqb Nat.eqb.
Proof. 
  unfold ieqb. constructor; intros n i Hin; constructor; intros m j Hjm.
  inversion Hin as [i' n' Hmini Hmaxi]; subst; clear Hin.
  inversion Hjm as [j' m' Hminj Hmaxj]; subst; clear Hjm. simpl in *.
  destruct (max i <? min j) eqn:Hij. assert (n =? m = false) as Hnm.
  rewrite Nat.eqb_neq. rewrite Nat.ltb_lt in Hij. omega. rewrite Hnm.
  auto with soundness. destruct (min i =? max i) eqn:Hii; eauto with soundness.
  destruct (max i =? min j) eqn:Hieqj; eauto with soundness.
  destruct (min j =? max j) eqn:Hjj; eauto with soundness. simpl.
  rewrite Nat.eqb_eq in Hii, Hieqj, Hjj. rewrite Hii in Hmini.
  assert (n = max i). apply Nat.le_antisymm; assumption. subst.
  rewrite Hjj in Hminj. assert (m = max j). apply Nat.le_antisymm; assumption.
  subst. rewrite Hjj in Hieqj. rewrite <- Nat.eqb_eq in Hieqj.
  rewrite Hieqj. eauto with soundness.
Qed.

Lemma ieqM_sound {M M'} `{SoundMonad M M'} : gamma ieqM eqbM.
Proof.
  unfold ieqM, eqbM. repeat constructor; eauto using ieqb_sound with soundness.
Qed.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound {M M'} `{SoundMonad M M'} :
  gamma build_interval build_natural.
Proof.
  unfold build_interval, build_natural.
  repeat constructor; simpl; gamma_destruct; eauto with soundness.
Qed.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound {M M'} `{SoundMonad M M'} : forall n,
  gamma (extract_interval n) (extract_natM n).
Proof.
  unfold extract_interval, extract_natM.
  intros. apply gamma_fun_apply. eauto with soundness.
  constructor. rewrite interval_min_refl. apply preorder_refl.
  rewrite interval_max_refl. apply preorder_refl.
Qed.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound {M M'} `{SoundMonad M M'} 
  {M_fail : MonadFail M} {M'_fail : MonadFail M'} : 
  gamma ensure_interval ensure_nat.
Proof.
  constructor; intros v v' Hv. inversion Hv; subst; simpl.
Admitted.
Hint Resolve ensure_interval_sound : soundness.

(* Soundness of operations on booleans *)

Lemma ab_and_sound :
  gamma and_ab andb.
Proof. 
  repeat constructor; intros. 
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.

Lemma ab_or_sound :
  gamma or_ab orb.
Proof. 
  repeat constructor; intros.
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.

Lemma ab_neg_sound :
  gamma neg_ab negb.
Proof. 
  repeat constructor; intros. 
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.

Lemma extract_bool_sound : forall x,
  gamma (VAbstrBool (extract_ab x)) (VBool x).
Proof. 
  intros. destruct x; eauto with soundness.
Qed.

(* Monadic operations on abstract booleans *)

Lemma ensure_abool_sound {M M'} `{SoundMonad M M'} 
  {M_fail : MonadFail M} {M'_fail : MonadFail M'} :
  gamma ensure_abool ensure_bool.
Proof. 
  constructor. intros a b Hab. unfold ensure_abool, ensure_bool.
Admitted.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound {M M'} `{SoundMonad M M'} :
  gamma neg_abM negbM.
Proof.
  unfold neg_abM, negbM. 
  repeat constructor; eauto using ab_neg_sound with soundness.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound {M M'} `{SoundMonad M M'} :
  gamma and_abM andbM.
Proof.
  unfold and_abM, andbM. 
  repeat constructor; eauto using ab_and_sound with soundness.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound {M M'} `{SoundMonad M M'} : forall b,
  gamma (extract_abM b) (extract_boolean b).
Proof. 
  unfold extract_abM, extract_boolean. destruct b; eauto with soundness.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound {M M'} `{SoundMonad M M'} :
  gamma build_abool build_boolean.
Proof.
  unfold build_abool, build_boolean.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_boolean_sound : soundness.

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

(* Soundness of interpreters *)

Definition ConcreteState := MaybeT (StateT store Maybe).

Definition AbstractState := 
  MaybeAT (StateT abstract_store Maybe).

Section joinable_abstract_state.
  Context {A : Type} `{Joinable A}.

  Definition join_abstract_state (st1 st2 : AbstractState A) : AbstractState A
    := λ st, join_op (st1 st) (st2 st).

  Lemma join_abstract_state_refl : ∀ st,
    join_abstract_state st st = st.
  Proof.
    intro st. ext. unfold join_abstract_state. rewrite join_refl.
    reflexivity.
  Qed.
  
  Lemma join_abstract_state_upper_bound_left : 
    ∀ a a' : (AbstractState A), preorder a (join_abstract_state a a').
  Proof.
    intros. unfold join_abstract_state. constructor. intros.
    apply join_upper_bound_left.
  Qed.

  Lemma join_abstract_state_upper_bound_right : 
    ∀ a a' : (AbstractState A), preorder a' (join_abstract_state a a').
  Proof.
    intros. unfold join_abstract_state. constructor. intros.
    apply join_upper_bound_right.
  Qed.

  Lemma join_abstract_state_assoc : ∀ a b c : (AbstractState A),
    join_abstract_state a (join_abstract_state b c) =
    join_abstract_state (join_abstract_state a b) c.
  Proof. 
    intros. unfold join_abstract_state. extensionality st.
    rewrite join_assoc. reflexivity.
  Qed.

  Global Instance joinable_abstract_state :
  Joinable (AbstractState A) :=
  {
    join_refl := join_abstract_state_refl;  
    join_upper_bound_left := join_abstract_state_upper_bound_left;
    join_upper_bound_right := join_abstract_state_upper_bound_right;
    join_assoc := join_abstract_state_assoc;
  }.
End joinable_abstract_state.

Lemma extract_build_val_sound : forall (v : cvalue),
  gamma 
    (extract_build_val (M:=AbstractState) 
        (valType:=avalue)
        (nat_inst:=isnat_parity AbstractState)
        (bool_inst:=(abstract_boolean_type)) v) 
    (extract_build_val (M:=ConcreteState) (valType:=cvalue) v).
Proof.
  destruct v; repeat constructor; eauto using extract_par_sound with soundness. 
  destruct b; auto with soundness.
Qed.
Hint Resolve extract_build_val_sound : soundness.

Theorem eval_expr_sound : forall a,
  gamma 
    (shared_eval_expr (M:=MaybeAT (StateT abstract_store Maybe)) (nat_inst:=isnat_parity AbstractState) 
      (bool_inst:=(abstract_boolean_type)) (S:=abstract_store) (valType:=avalue) a) 
    (shared_eval_expr (M:=ConcreteState) (valType:=cvalue) a).
Proof.
  intros. induction a; repeat constructor; simpl; intros.
  - auto using gamma_fun_apply with soundness.
  - auto using gamma_fun_apply with soundness. gamma_destruct.
    auto.
  - intros. repeat apply gamma_fun_apply; eauto with soundness.
  - repeat apply gamma_fun_apply. admit. auto. constructor; intros.
    repeat apply gamma_fun_apply. admit. auto. constructor; intros.
    repeat apply gamma_fun_apply. admit. admit. auto. admit. auto.
Admitted.
Hint Resolve eval_expr_sound : soundness.

Section sound_if.
  Context {M M' : Type → Type} `{SoundMonad M M'} `{MonadFail M'}.
  Hypothesis M'_joinable : ∀ (T : Type) {T_pre : PreorderedSet T}, 
    Joinable T → Joinable (M' T).

Lemma sound_if_op : 
  gamma (eval_if_abstract (M:=M')) (eval_if (M:=M)).
Proof.
  constructor; intros b ab Hab. constructor; intros m m' Hm. 
  constructor; intros m2 m2' Hm2. 
  destruct b, ab; simpl; eauto with soundness. inversion Hab. discriminate.
  apply gamma_join_left. apply Hm. inversion Hab. discriminate.
  apply gamma_join_right. apply Hm2.
Qed.
End sound_if.

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
                    (nat_inst:=isnat_parity AbstractState)
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

