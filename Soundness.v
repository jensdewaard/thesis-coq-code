Require Export Base.
Require Export Instances.Galois.
Require Import Classes.Galois.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.PeanoNat.
Require Import Instances.Except.
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
Require Import Classes.IsBool.

Hint Extern 0 (γ _ _) => progress gamma_destruct : soundness.

(* Soundness of unit *)
Lemma gamma_unit_sound :
  γ tt tt.
Proof. constructor.  Qed.
Hint Resolve gamma_unit_sound : soundness.

(* Soundness of functions *)
Lemma gamma_fun_apply {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') x x' :
  γ f f' -> γ x x' -> γ (f x) (f' x').
Proof. 
  eauto with soundness.
Qed.
Hint Extern 3 (γ (?f ?x) (?g ?y)) => apply gamma_fun_apply : soundness.

(* Soundness of monadic operations *)
Instance some_sound : return_sound option option.
Proof.
  unfold return_sound. eauto with soundness.
Qed.

Instance bind_option_sound : bind_sound option option.
Proof.
  unfold bind_sound. unfold bindM; simpl. intros. destruct m, m'; 
  eauto with soundness.
Qed.

Instance someA_sound : return_sound optionA option.
Proof.
  unfold return_sound; eauto with soundness.
Qed.

Instance bind_optionA_sound : bind_sound optionA option.
Proof.
  unfold bind_sound; intros. unfold bindM; simpl. destruct m, m'; eauto with
    soundness.
  - simpl. gamma_destruct. apply H1 in H3. destruct (f a), (f' a0); eauto with
    soundness.
  - simpl. destruct (f a); eauto with soundness.
Qed.

Instance return_state_sound {S S' : Type} {GS : Galois S S'} : 
  return_sound (State S) (State S').
Proof.
  unfold return_sound; unfold returnM; simpl; intros.
  constructor. eauto with soundness.
Qed.

Instance bind_state_sound {S S' : Type} {GS : Galois S S'} :
  bind_sound (State S) (State S').
Proof.
  unfold bind_sound, bindM; simpl; intros.
  constructor; intros. unfold bind_state. destruct H.
  apply H in H1. destruct (f0 a), (g a'). eauto with soundness.
Qed.

Section stateT.
  Context {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}.
  Context {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}.
  Context {S S' : Type} {GS : Galois S S'}.
  Context {RS : return_sound M M'}.
  Context {BS : bind_sound M M'}.

  Global Instance return_stateT_sound : 
    return_sound (StateT S M) (StateT S' M').
  Proof.
    unfold return_sound, returnM; simpl. unfold return_stateT; intros. 
    eauto with soundness.
  Qed.

  Global Instance bind_stateT_sound : bind_sound (StateT S M) (StateT S' M').
  Proof.
    unfold bind_sound, bindM; simpl; unfold bind_stateT; intros.
    constructor; intros. apply bindM_sound. eauto with soundness.
    constructor. intros p q Hpq. destruct p, q. eauto with soundness.
  Qed.
End stateT.

Section optionT.
  Context {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}.
  Context {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}.
  Context {RS : return_sound M M'}.
  Context {BS : bind_sound M M'}.

  Global Instance someT_sound : return_sound (optionT M) (optionT M').
  Proof.
    unfold return_sound, returnM; simpl. intros. eauto with soundness.
  Qed.

  Global Instance bind_optionT_sound : bind_sound (optionT M) (optionT M').
  Proof.
    unfold bind_sound, bindM; simpl; intros. 
    unfold bind_optionT. eapply BS. assumption. constructor.
    intros. destr; eauto with soundness. 
    admit.
  Admitted.
End optionT.

Section optionAT.
  Context {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}.
  Context {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}.
  Context {RS : return_sound M M'}. 
  Context {BS : bind_sound M M'}.

  Global Instance someAT_sound : return_sound (optionAT M) (optionT M').
  Proof.
    unfold return_sound, returnM; simpl.
    eauto with soundness.
  Qed.

  Global Instance bind_optionAT : bind_sound (optionAT M) (optionT M').
  Proof.
    unfold bind_sound. unfold bindM; simpl.
    intros. unfold bind_optionAT, bind_optionT, optionAT, optionT.
    unfold bind_sound.
    apply bindM_sound; try assumption.
    constructor; intros a a' Ha.
    inversion Ha; subst; eauto with soundness.
    - rewrite <- bind_id_right. admit.
    - rewrite <- bind_id_right. apply bindM_sound; eauto with soundness.
      constructor. intros. destruct a, a'; eauto with soundness.
  Admitted.

  Lemma lift_optionAT_sound {A A'} `{Galois A A'} :
    γ (lift_optionAT (M:=M) (A:=A)) (lift_optionT (A:=A')).
  Proof.
    unfold lift_optionAT, lift_optionT, optionAT, optionT.
    repeat constructor. intros. apply bindM_sound; eauto with soundness.
  Qed.
End optionAT.

(* Soundness of interpreters *)

Definition avalue := ((parity+⊤)+(abstr_bool+⊤))%type.
Definition ConcreteState := optionT (StateT (store cvalue) option).

Definition AbstractState := optionAT (StateT (store (avalue+⊤)) option).

Theorem eval_expr_sound : forall a,
  γ 
    (shared_eval_expr (M:=AbstractState) (valType:=avalue+⊤)
    (boolType:=abstr_bool+⊤) (natType:=parity+⊤) a) 
    (shared_eval_expr (M:=ConcreteState) (valType:=cvalue) 
    (boolType:=bool) (natType:=nat) a).
Proof.
  intros. induction a; repeat constructor; simpl; intros. 
  - auto with soundness.
  - auto with soundness. 
  - auto with soundness.
  - Set Printing Implicit. About γ.

    apply gamma_fun_apply. 2: assumption.
    admit.
  - admit.
Admitted.
Hint Resolve eval_expr_sound : soundness.

Theorem sound_interpreter: ∀ c, 
  γ (shared_ceval (M:=AbstractState) (valType:=avalue+⊤)
    (boolType:=(abstr_bool+⊤)) (natType:=(parity+⊤)) c) 
    (shared_ceval (M:=ConcreteState) (valType:=cvalue)
    (boolType:=bool) (natType:=nat) c).
Proof.
  induction c; simpl. 
  - eauto with soundness.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness.
Admitted.

