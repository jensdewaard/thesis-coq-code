Require Export Base.
Require Export Instances.Galois.
Require Import Classes.Galois.
Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Classes.PreorderedSet.
Require Import Classes.SoundMonad.
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
Require Import Psatz.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.State.
Require Import Types.Stores.

Hint Extern 0 (γ _ _) => progress gamma_destruct : soundness.

Axiom gamma_pure_none : ∀ {M M' : Type → Type} `{Monad M, Monad M'} {A A' :
  Type}  `{Galois (M A) (M' (option A'))} (c : M A), γ (returnM (M:=M') None) c.
Hint Resolve gamma_pure_none : soundness.

(* Soundness of unit *)
Lemma gamma_unit_sound :
  γ tt tt.
Proof. constructor.  Qed.
Hint Resolve gamma_unit_sound : soundness.

(* Soundness of functions *)
Lemma gamma_fun_apply {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') x x' :
  γ f' f -> γ x' x -> γ (f' x') (f x).
Proof. 
  eauto with soundness.
Qed.
Hint Extern 3 (γ (?f ?x) (?g ?y)) => apply gamma_fun_apply : soundness.

Lemma gamma_fun_applied {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') :
      (forall x x', γ x' x -> γ (f' x') (f x)) ->
        γ f' f.
Proof. 
  eauto with soundness.
Qed.
(*Hint Resolve gamma_fun_applied : soundness.*)

(* Soundness of monadic operations *)
Lemma some_sound : ∀ (A A' : Type) `{A_galois : Galois A A'},
  γ (Some (A:=A')) (Some (A:=A)).
Proof.
  eauto with soundness.
Qed.

Lemma bind_option_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  γ (bindM (M:=option) (A:=A') (B:=B')) 
        bindM.
Proof.
  unfold bindM; simpl.
  repeat constructor. intros.
  destruct a', a; eauto with soundness.
Qed.
Hint Resolve bind_option_sound : soundness.

Instance option_sound : SoundMonad option option :=
{
  return_sound := some_sound;
  bind_sound := bind_option_sound;
}.

Lemma someA_sound : ∀ A A' `{A_galois : Galois A A'},
  γ (SomeA (A:=A')) Some.
Proof.
  eauto with soundness.
Qed.

Lemma bind_optionA_sound (A A' B B' : Type) `{Galois A A', Galois B B'} :
  γ (bindM (M:=optionA) (A:=A') (B:=B')) bindM.
Proof.
  unfold bindM; simpl.
  constructor; intros ma ma' Hma. constructor; intros mf mf' Hmf.
  destruct ma, ma' as [a'| |a']; simpl; eauto with soundness.
  inversion Hma as [Ha |? |? |?? Ha];subst.
  inversion Hmf as [?? Hf]; subst.
  apply Hf in Ha. all: destruct (mf' a'); eauto with soundness.
Qed.

Instance abstract_option_sound : SoundMonad option optionA :=
{
  return_sound := someA_sound;
  bind_sound := bind_optionA_sound;
}.

Lemma bind_state_sound {S S'} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'},
  γ
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
    γ (return_stateT (S:=S') (M:=M') (A:=A')) (return_stateT (A:=A)).
  Proof.
    unfold return_stateT. eauto 10 using return_sound with soundness.
  Qed.

  Lemma bind_stateT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
    γ (bind_stateT (A:=A') (B:=B') (S:=S') (M:=M')) bind_stateT.
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

Section optionT.
  Context {M M' : Type → Type} `{SoundMonad M M'}.

  Lemma someT_sound : ∀ A A' `{Galois A A'},
    γ (λ a, returnM (M:=M') (Some (A:=A') a)) (λ a, returnM (M:=M) (Some a)).
  Proof. 
    intros. constructor. intros. eapply gamma_fun_apply; eauto with soundness. 
  Qed.

  Lemma bind_optionT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
    γ (bind_optionT (A:=A') (B:=B') (M:=M')) bind_optionT.
  Proof. 
    intros. unfold bind_optionT, optionT. repeat constructor; intros. 
    repeat eapply gamma_fun_apply; eauto with soundness.
  Qed.

  Global Instance optionT_sound : SoundMonad (optionT M) (optionT M') :=
  {
    return_sound := someT_sound;
    bind_sound := bind_optionT_sound;
  }.
End optionT.

Section optionAT.
  Context {M M' : Type → Type} `{SoundMonad M M'}.

  Lemma someAT_sound : ∀ A A' `{Galois A A'},
    γ (λ a : A', returnM (M:=M') (SomeA a)) (λ a, returnM (M:=M) (Some a)).
  Proof. eauto with soundness. Qed.

  Lemma bind_optionAT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
    γ (bind_optionAT (A:=A') (B:=B') (M:=M')) bind_optionT.
  Proof.
    intros. constructor; intros Ma Ma' HMa.
    constructor; intros f f' Hf'. unfold bind_optionAT, bind_optionT.
    unfold optionT, optionAT.
    repeat apply gamma_fun_apply; eauto with soundness. 
    constructor; intros m m' Hm. 
    destruct m; inversion Hm; subst; eauto with soundness.
    - rewrite <- bind_id_right. eapply gamma_fun_apply.
      eauto with soundness.
      constructor; intros m m' Hm'. destruct m'; eauto with soundness.
    - eauto with soundness. admit.
  Admitted.

  Lemma lift_optionAT_sound {A A'} `{Galois A A'} :
    γ (lift_optionAT (M:=M') (A:=A')) (lift_optionT (A:=A)).
  Proof.
    unfold lift_optionAT, lift_optionT, optionAT, optionT.
    repeat constructor. intros.
    repeat eapply gamma_fun_apply; eauto with soundness.
  Qed.

  Global Instance optionAT_sound : SoundMonad (optionT M) (optionAT M') :=
  {
    return_sound := someAT_sound;
    bind_sound := bind_optionAT_sound;
  }.
End optionAT.

(* Soundness of parity operations *)

Lemma gamma_par_extract_n_n : forall n,
  γ (extract_par n) n.
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
  γ parity_plus plus.
Proof.
  autounfold with soundness. repeat constructor. intros.
  destruct a', a'0; eauto with soundness.
Qed.

Lemma parity_mult_sound :
  γ parity_mult mult.
Proof. 
  autounfold with soundness. repeat constructor; intros.
  destruct a', a'0; gamma_destruct; try constructor; eauto with soundness.
Qed.

Hint Rewrite Nat.eqb_eq : soundness.
Lemma parity_eq_sound :
  γ parity_eq Nat.eqb. 
Proof. 
  repeat constructor. intros. destruct a', a'0; simpl; try constructor.
  gamma_destruct. assert (a ≠ a0). unfold not. intro; subst.
  apply (Nat.Even_Odd_False a0); auto. rewrite Nat.eqb_neq; auto.
  gamma_destruct. assert (a ≠ a0). unfold not. intro; subst.
  apply (Nat.Even_Odd_False a0); auto. rewrite Nat.eqb_neq; auto.
Qed.

Lemma extract_par_sound : forall n,
  γ (extract_par n) n.
Proof. 
  intros. unfold extract_par. destruct (Nat.even n) eqn:Hpar; repeat constructor.
  rewrite <- Nat.even_spec; auto.
  rewrite <- Nat.odd_spec. unfold Nat.odd. rewrite Hpar. reflexivity.
Qed.

(* Monadic versions of parity operations *)
Lemma ensure_par_sound {M M'} `{SoundMonad M M'} 
  {M'_fail : MonadFail M'} {M_fail : MonadFail M} :
  γ (ensure_par (M:=M')) ensure_nat.
Proof.
  constructor; intros a a' Hgamma. destruct a; inv Hgamma; subst; simpl; eauto
  with soundness.
Admitted.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound {M M'} `{SoundMonad M M'} : forall n,
  γ (extract_parM n) (extract_natM n). 
Proof. 
  intros. unfold extract_parM, extract_natM. 
  repeat eapply gamma_fun_apply; eauto using extract_par_sound with soundness. 
Qed. 
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound {M M'} `{SoundMonad M M'} : 
  γ pplusM plusM.
Proof. 
  unfold pplusM, plusM.
  repeat constructor; eauto using parity_plus_sound with soundness. 
Qed.
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound {M M'} `{SoundMonad M M'} :
  γ pmultM multM.
Proof.
  unfold pmultM, multM.
  repeat constructor; eauto using parity_mult_sound with soundness. 
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound {M M'} `{SoundMonad M M'} :
  γ peqM eqbM.
Proof.
  unfold peqM, eqbM.
  repeat constructor; eauto using parity_eq_sound with soundness.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound {M M'} `{SoundMonad M M'} :
  γ pleM lebM.
Proof.
  unfold pleM, lebM.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound {M M'} `{SoundMonad M M'} :
  γ build_parity build_natural.
Proof.
  unfold build_parity, build_natural.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on intervals *)
Lemma iplus_sound : γ iplus plus.
Proof.
  repeat constructor; gamma_destruct; simpl in *; lia.
Qed.

Lemma iplusM_sound {M M'} `{SoundMonad M M'} :
  γ iplusM plusM.
Proof. 
  unfold iplusM, plusM.
  repeat constructor; intros. eauto using iplus_sound with soundness.
Qed.
Hint Resolve iplusM_sound : soundness.

Lemma imult_sound : γ imult mult.
Proof.
  repeat constructor. 
  - rewrite interval_min_mult. gamma_destruct; simpl in *.
    apply Coq.Arith.Mult.mult_le_compat; auto.
  - rewrite interval_max_mult. gamma_destruct; simpl in *.
    apply Coq.Arith.Mult.mult_le_compat; auto.
Qed.

Lemma imultM_sound {M M'} `{SoundMonad M M'} :
  γ imultM multM.
Proof.
  unfold imultM, multM.
  repeat constructor; intros. eauto using imult_sound with soundness.
Qed.
Hint Resolve imultM_sound : soundness.

Lemma ileqb_sound : γ ileqb leb.
Proof.
  constructor; intros n i Hn; constructor; intros m j Hm.
  unfold ileqb. gamma_destruct; simpl in *.
  destruct (max i <? min j) eqn:Hij. 
  rewrite Nat.ltb_lt in Hij.
  assert (n <=? m = true) as Hnm. rewrite Nat.leb_le. lia. rewrite Hnm.
  auto with soundness. destruct (max j <? min i) eqn:Hji.
  rewrite Nat.ltb_lt in Hji. rewrite Nat.ltb_ge in Hij.
  assert (n <=? m = false) as Hnm. apply leb_correct_conv. lia.
  rewrite Hnm. constructor. reflexivity. constructor.
Qed.

Lemma ilebM_sound {M M'} `{SoundMonad M M'} :
  γ ileM lebM.
Proof.
  unfold ileM, lebM.
  repeat constructor; intros. eauto using ileqb_sound with soundness.
Qed.
Hint Resolve ileqb_sound : soundness.

Lemma ieqb_sound : γ ieqb Nat.eqb.
Proof. 
  unfold ieqb. constructor; intros n i Hin; constructor; intros m j Hjm.
  inversion Hin as [i' n' Hmini Hmaxi]; subst; clear Hin.
  inversion Hjm as [j' m' Hminj Hmaxj]; subst; clear Hjm. simpl in *.
  destruct (max i <? min j) eqn:Hij. assert (n =? m = false) as Hnm.
  rewrite Nat.eqb_neq. rewrite Nat.ltb_lt in Hij. lia. rewrite Hnm.
  auto with soundness. destruct (min i =? max i) eqn:Hii; eauto with soundness.
  destruct (max i =? min j) eqn:Hieqj; eauto with soundness.
  destruct (min j =? max j) eqn:Hjj; eauto with soundness. simpl.
  rewrite Nat.eqb_eq in Hii, Hieqj, Hjj. rewrite Hii in Hmini.
  assert (n = max i). apply Nat.le_antisymm; assumption. subst.
  rewrite Hjj in Hminj. assert (m = max j). apply Nat.le_antisymm; assumption.
  subst. rewrite Hjj in Hieqj. rewrite <- Nat.eqb_eq in Hieqj.
  rewrite Hieqj. eauto with soundness.
Qed.

Lemma ieqM_sound {M M'} `{SoundMonad M M'} : γ ieqM eqbM.
Proof.
  unfold ieqM, eqbM. repeat constructor; eauto using ieqb_sound with soundness.
Qed.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound {M M'} `{SoundMonad M M'} :
  γ build_interval build_natural.
Proof.
  unfold build_interval, build_natural.
  repeat constructor; simpl; gamma_destruct; eauto with soundness.
Qed.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound {M M'} `{SoundMonad M M'} : forall n,
  γ (extract_interval n) (extract_natM n).
Proof.
  unfold extract_interval, extract_natM.
  intros. apply gamma_fun_apply. eauto with soundness. repeat constructor.
Qed.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound {M M'} `{SoundMonad M M'} 
  {M_fail : MonadFail M} {M'_fail : MonadFail M'} : 
  γ ensure_interval ensure_nat.
Proof.
  constructor; intros v v' Hv. inversion Hv; subst.
Admitted.
Hint Resolve ensure_interval_sound : soundness.

(* Soundness of operations on booleans *)

Lemma ab_and_sound :
  γ and_ab andb.
Proof. 
  repeat constructor; intros. 
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.

Lemma ab_or_sound :
  γ or_ab orb.
Proof. 
  repeat constructor; intros.
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.

Lemma ab_neg_sound :
  γ neg_ab negb.
Proof. 
  repeat constructor; intros. 
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.

Lemma extract_bool_sound : forall x,
  γ (VAbstrBool (extract_ab x)) (VBool x).
Proof. 
  intros. destruct x; eauto with soundness.
Qed.

(* Monadic operations on abstract booleans *)

Lemma ensure_abool_sound {M M'} `{SoundMonad M M'} 
  {M_fail : MonadFail M} {M'_fail : MonadFail M'} :
  γ ensure_abool ensure_bool.
Proof. 
  constructor. intros a b Hab. unfold ensure_abool, ensure_bool.
Admitted.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound {M M'} `{SoundMonad M M'} :
  γ neg_abM negbM.
Proof.
  unfold neg_abM, negbM. 
  repeat constructor; eauto using ab_neg_sound with soundness.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound {M M'} `{SoundMonad M M'} :
  γ and_abM andbM.
Proof.
  unfold and_abM, andbM. 
  repeat constructor; eauto using ab_and_sound with soundness.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound {M M'} `{SoundMonad M M'} : forall b,
  γ (extract_abM b) (extract_boolean b).
Proof. 
  unfold extract_abM, extract_boolean. destruct b; eauto with soundness.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound {M M'} `{SoundMonad M M'} :
  γ build_abool build_boolean.
Proof.
  unfold build_abool, build_boolean.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_boolean_sound : soundness.

(* Soundness of operations on stores *)

(*Lemma store_get_sound : forall s,
  γ (abstract_store_get s) (store_get s).
Proof.
  repeat constructor. inv H0. apply H1. inv H0; assumption.
  inv H; assumption.
Qed.
Hint Resolve store_get_sound : soundness.*)

Lemma t_update_sound : forall (ast : abstract_store) (st : store) x p n,
  γ ast st ->
  γ p n ->
  γ (t_update ast x p) (t_update st x n).
Proof. 
  unfold t_update. repeat constructor; eauto with soundness.
  intros x'. destruct (beq_string x x'); eauto with soundness.
Qed.

(* Soundness of interpreters *)

Definition ConcreteState := optionT (StateT store (optionT Identity)).

Definition AbstractState := 
  optionAT (StateT abstract_store (optionT Identity)).

Lemma extract_build_val_sound : forall (v : cvalue),
  γ 
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
  γ 
    (shared_eval_expr (M:=AbstractState) (nat_inst:=isnat_parity AbstractState) 
      (bool_inst:=(abstract_boolean_type)) (valType:=avalue) a) 
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
  γ (eval_if_abstract (M:=M')) (eval_if (M:=M)).
Proof.
  constructor; intros b ab Hab. constructor; intros m m' Hm. 
  constructor; intros m2 m2' Hm2. 
  destruct b, ab; simpl; eauto with soundness. inversion Hab. discriminate.
  apply gamma_join_left. apply Hm. inversion Hab. discriminate.
  apply gamma_join_right. apply Hm2.
Qed.
End sound_if.

(*Lemma sound_eval_catch :
  γ (eval_catch_abstract) (eval_catch).
Proof.
  intros s1' s1 H s2' s2. intros H0 a b H1. 
  unfold γ in H, H0; simpl in H, H0; unfold gamma_fun in H, H0.
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
    + unfold γ in H1; simpl in H1.
      eapply widen. apply join_upper_bound_right. unfold gamma; simpl.
      pose proof H1. apply H0 in H1.  apply H1.
Qed.
Hint Resolve sound_eval_catch : soundness.
*)
  (*
Lemma sound_fail : 
  γ fail_abstract fail.
Proof.
  unfold fail_abstract, fail. intros ???. auto.
Qed.
Hint Resolve sound_fail : soundness.
*)

Theorem sound_interpreter:
  forall c, γ (shared_ceval 
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

