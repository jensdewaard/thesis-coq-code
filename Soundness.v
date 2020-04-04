Require Export Base.
Require Export Instances.Galois.
Require Import Classes.Galois.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Classes.PreorderedSet.
Require Import Classes.SoundMonad.
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
Lemma some_sound {A A' : Type} `{Galois A A'} : ∀ a a', 
  γ a a' →
  γ (Some a) (Some a').
Proof.
  eauto with soundness.
Qed.

Lemma bind_option_sound {A A' B B'} `{Galois A A', Galois B B'} : 
  ∀ m m' f f', 
  γ m m' → γ f f' →
  γ (bind_option m f) (bind_option m' f').
Proof.
  unfold bindM; simpl.
  repeat constructor. intros.
  destruct m, m'; eauto with soundness.
Qed.
Hint Resolve bind_option_sound : soundness.

Lemma someA_sound {A A' : Type} `{GA : Galois A A'} : ∀ (a : A) (a' : A'),
  γ a a' → 
  γ (SomeA a) (Some a').
Proof.
  eauto with soundness.
Qed.

Lemma bind_optionA_sound (A A' B B' : Type) `{Galois A A', Galois B B'} :
  ∀ (m : optionA A) (m' : option A') 
    (f : A → optionA B) (f' : A' → option B'),
  γ m m' → γ f f' →
  γ (bind_optionA m f) (bind_option m' f').
Proof.
  intros m m' f f' Hm Hf. destruct m, m'; eauto with soundness.
  - inversion Hm; subst; clear Hm. gamma_destruct. apply H1 in H3.
    cbv. destruct (f a), (f' a0); simpl; try constructor;  eauto with
      soundness.
  - inversion Hm; subst; clear Hm. gamma_destruct. cbv. destruct (f a);
    constructor.
Qed.

Lemma bind_state_sound {S S'} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'},
  γ
    (bind_state (S:=S) (A:=A) (B:=B))
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
  Context {M M' : Type → Type} `{Monad M, Monad M'}.
  Context {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}.
  Context {S S' : Type} `{Galois S S'}.
  Context {RS : return_sound M M'}.
  Context {BS : bind_sound M M'}.

  Lemma return_stateT_sound {A A'} `{Galois A A'} : 
    γ (return_stateT (S:=S) (M:=M) (A:=A)) 
      (return_stateT (S:=S') (M:=M') (A:=A')).
  Proof.
    unfold return_stateT. constructor. intros a a' Ha. constructor.
    intros s s' Hs. eauto with soundness.
  Qed.

  Lemma bind_stateT_sound {A A' B B'} `{Galois A A', Galois B B'} : 
    ∀ (m : StateT S M A) (m' : StateT S' M' A')
      (f : A → StateT S M B) (f' : A' → StateT S' M' B'),
    γ m m' → γ f f' → 
    γ (bind_stateT m f) (bind_stateT m' f').
  Proof.
    intros. unfold bind_stateT. repeat constructor; intros s s' Hs. 
    apply bindM_sound.
    apply gamma_fun_apply; assumption. constructor. intros p p' Hp.
    destruct p, p'. eauto with soundness.
  Qed.
End stateT.

Section optionT.
  Context {M M' : Type → Type}.
  Context `{RS : return_sound M M'}.
  Context {BS : bind_sound M M'}.

  Lemma someT_sound {A A'} `{Galois A A'} : ∀ a a',
    γ a a' →
    γ (returnM (M:=M) (Some a)) (returnM (M:=M') (Some a')).
  Proof. 
    intros. eapply gamma_fun_apply; eauto with soundness. 
  Qed.

  Lemma bind_optionT_sound {A A' B B'} `{Galois A A', Galois B B'} : 
    ∀ (m : optionT M A) (m' : optionT M' A')
      (f : A → optionT M B) (f' : A' → optionT M' B'),
    γ m m' → γ f f' → 
    γ (bind_optionT m f) (bind_optionT m' f').
  Proof. 
    intros. eapply BS. assumption. constructor; intros a a' Ha.
    gamma_destruct; eauto with soundness. admit.
  Admitted.
End optionT.

Section optionAT.
  Context {M M' : Type → Type}.
  Context `{RS : return_sound M M'} {BS : bind_sound M M'}.

  Lemma someAT_sound {A A'} `{Galois A A'} : ∀ a a',
    γ a a' →
    γ (returnM (SomeA a)) (returnM (Some a')).
  Proof. eauto with soundness. Qed.

  Lemma bind_optionAT_sound {A A' B B'} `{Galois A A', Galois B B'} : 
    ∀ (m : optionAT M A) (m' : optionT M' A') 
      (f : A → optionAT M B) (f' : A' → optionT M' B'),
    γ m m' → γ f f' →
    γ (bind_optionAT m f) (bind_optionT m' f').
  Proof.
    intros. unfold bind_optionAT, bind_optionT, optionAT, optionT.
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
Definition ConcreteState := optionT (StateT (store cvalue) (optionT Identity)).

Definition AbstractState := optionAT (StateT (store (avalue+⊤)) (optionT Identity)).

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
  - apply gamma_fun_apply. 2: assumption. admit.
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

