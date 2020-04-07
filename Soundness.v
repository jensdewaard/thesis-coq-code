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
  unfold bind_sound. intros A A' B B' GA GB m m' f f' Hm Hf. 
  unfold bindM; simpl. 
  destruct m as [a | |], m' as [a' |]; eauto with soundness.
  - simpl. 
    inversion Hm as [ | | | a1' a1 Ha H1 H0  ]; subst.
    apply Hf in Ha. destruct (f a), (f' a'); eauto with soundness.
  - simpl. destruct (f a); eauto with soundness.
Qed.

Instance return_state_sound {S S' : Type} {GS : Galois S S'} : 
  return_sound (State S) (State S').
Proof.
  unfold return_sound; unfold returnM; simpl; intros. unfold return_state.
  constructor; simpl; eauto with soundness. 
Qed.

Instance bind_state_sound {S S' : Type} {GS : Galois S S'} :
  bind_sound (State S) (State S').
Proof.
  unfold bind_sound, bindM; simpl. 
  intros A A' B b' GA GB m m' f f' Hm Hf. 
  unfold bind_state. intros s s' Hs. apply Hm in Hs.
  destruct (m s), (m' s'). inversion Hs; subst. simpl in *. eauto with
    soundness.
Qed.

Section stateT.
  Context (M M' : Type → Type) {MM : Monad M} {MM' : Monad M'}.
  Context {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}.
  Context {S S' : Type} {GS : Galois S S'}.
  Context {RS : return_sound M M'}.
  Context {BS : bind_sound M M'}.

  Global Instance return_stateT_sound : 
    return_sound (StateT S M) (StateT S' M').
  Proof.
    unfold return_sound, returnM; simpl. unfold return_stateT. 
    intros A A' GA a a' Ha s s' Hs. eauto with soundness.
  Qed.

  Global Instance bind_stateT_sound : bind_sound (StateT S M) (StateT S' M').
  Proof.
    unfold bind_sound, bindM; simpl; unfold bind_stateT; intros.
    intros s s' Hs. apply bindM_sound; eauto with soundness.
    intros p q Hpq. destruct p, q; eauto with soundness.
  Qed.
End stateT.

Section optionT.
  Context (M M' : Type → Type) {MM : Monad M} {MM' : Monad M'}.
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
    unfold bind_optionT. eapply BS. assumption. intros o o' Ho.
    destr; eauto with soundness. subst.
  Admitted.
End optionT.

Section optionAT.
  Global Instance someAT_sound : ∀ (M M' : Type → Type) {MM : Monad M} {MM' :
    Monad M'} {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')},
    return_sound M M' → return_sound (optionAT M) (optionT M').
  Proof.
    unfold return_sound, returnM; simpl.
    eauto with soundness.
  Qed.

  Global Instance bind_optionAT_sound : ∀ (M M' : Type → Type) {MM : Monad M}
  {MM' : Monad M'} {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')},
    return_sound M M' → 
    bind_sound M M' → 
    bind_sound (optionAT M) (optionT M').
  Proof.
    intros M M' MM MM' GM RS BS.
    unfold bind_sound. unfold bindM; simpl.
    intros A A' B B' GA GB m m' f f' Hm Hf. 
    unfold bind_optionAT, bind_optionT, optionAT, optionT.
    unfold bind_sound in BS. eapply BS. assumption.
    intros a a' Ha.
    inversion Ha; subst; eauto with soundness.
    - rewrite <- bind_id_right. admit.
    - rewrite <- bind_id_right. eapply BS; auto with soundness.
      intros a' a Ha'. destruct a, a'; eauto with soundness.
  Admitted.
End optionAT.

(* Soundness of interpreters *)

Definition avalue := ((parity+⊤)+(abstr_bool+⊤))%type.
Definition ConcreteState := optionT (StateT (store cvalue) option).
Definition ConcreteState' A := (string → nat + bool) → option (option A * (string
  → nat + bool)).

Definition AbstractState := optionAT (StateT (store (avalue+⊤)) option).
Definition AbstractState' A := (string → (parity +⊤ + abstr_bool +⊤) +⊤)
         → option (optionA A * (string → (parity +⊤ + abstr_bool +⊤) +⊤)).

Theorem eval_expr_sound : ∀ (e : expr), 
  γ 
    (shared_eval_expr (M:=AbstractState) (valType:=avalue+⊤) e)
    (shared_eval_expr (M:=ConcreteState) (valType:=cvalue) e).
Proof.
  eapply shared_eval_expr_sound; eauto with soundness.
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

