Require Import Classes.Joinable.
Require Export Base.
Require Import Classes.Monad Classes.Monad.MonadState 
  Types.State Classes.Galois Types.Option.

Implicit Type ST : Type.
Implicit Type M : Type → Type.
Generalizable Variables ST M.

Instance store_state : MonadState ST (State ST) := {
  get := λ st, (st, st);
  put := λ st, λ _, (tt, st);
}.

Instance get_store_state_sound {ST ST' : Type} {GS : Galois ST ST'} : 
  get_state_sound (State ST) (State ST').
Proof.
  unfold get_state_sound. constructor; assumption.
Qed.
Hint Resolve get_store_state_sound : soundness.

Instance store_stateT `{MM : Monad M} : MonadState ST (StateT ST M) := {
  get := λ st, returnM (st, st);
  put := λ st, λ _, returnM (tt, st);
}.

Instance get_store_stateT_sound {ST ST' : Type} {GS : Galois ST ST'} 
  {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} :
  return_sound M M' →
  get_state_sound (StateT ST M) (StateT ST' M').
Proof.
  intros RS. intros a a' Ha. apply returnM_sound. eauto with soundness.
Qed.
Hint Resolve get_store_stateT_sound : soundness.

Instance put_store_stateT_sound {ST ST' : Type} {GS : Galois ST ST'}
  {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} :
  return_sound M M' →
  put_state_sound (StateT ST M) (StateT ST' M').
Proof.
  intros RS s s' Hs. cbn. intros ???. apply RS. constructor; cbn.
  constructor. assumption.
Qed.
Hint Resolve put_store_stateT_sound : soundness.

Instance store_optionT {ST} {M} {MM : Monad M} {MS : MonadState ST M} :
  MonadState ST (optionT M) := {
  get := get >>= λ a, returnM (Some a);
  put := λ st, put st ;; returnM (Some tt);
}.

Instance get_store_optionT_sound {ST ST' : Type} {GST : Galois ST ST'}
  {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {MS : MonadState ST M} {MS' : MonadState ST' M'} :
  bind_sound M M' →
  return_sound M M' → 
  get_state_sound M M' →
  get_state_sound (optionT M) (optionT M').
Proof.
  intros BS RS GS.
  unfold get_state_sound. unfold get; simpl. 
  eapply BS; auto.
  intros a a' Ha. eauto with soundness.
Qed.
Hint Resolve get_store_optionT_sound : soundness.


Instance store_optionAT {ST M} {MM : Monad M} {MS : MonadState ST M} 
  {JS : joinsecondable M} :
  MonadState ST (optionAT M) := {
  get := get >>= λ a, returnM (SomeA a);
  put := λ st, put st ;; returnM (SomeA tt);
}.

Instance get_store_optionAT_sound {ST ST' : Type} {GST : Galois ST ST'}
  {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}
  {JS : joinsecondable M}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {MS : MonadState ST M} {MS' : MonadState ST' M'} :
  bind_sound M M' →
  return_sound M M' →
  get_state_sound M M' → 
  get_state_sound (optionAT M) (optionT M').
Proof.
  intros BS RS GS.
  unfold get_state_sound, get; simpl. 
  eapply BS. auto. intros a a' Ha. eauto with soundness.
Qed.
Hint Resolve get_store_optionAT_sound : soundness.

Instance put_store_optionAT_sound {ST ST' : Type} {GST : Galois ST ST'}
  {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}
  {JS : joinsecondable M} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {MS : MonadState ST M} {MS' : MonadState ST' M'} :
  return_sound M M' →
  bind_sound M M' →
  put_state_sound M M' →
  put_state_sound (optionAT M) (optionT M').
Proof.
  intros RS BS PS s s' Hs. cbn. eapply BS.  apply PS. assumption.
  intros ???. apply RS. constructor. constructor.
Qed.
Hint Resolve put_store_optionAT_sound : soundness.
