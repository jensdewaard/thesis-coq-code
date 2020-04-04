Require Export Base.
Require Import Classes.Monad Classes.Monad.MonadState Instances.Monad
  Types.State.

Implicit Type ST : Type.
Implicit Type M : Type → Type.
Generalizable Variables ST M.

Instance store_state : MonadState ST (State ST).
Proof.
  split.
  exact (λ st : ST, (st, st)).
  exact (λ st : ST, λ _ : ST, (tt, st)).
Defined.

Instance store_stateT `{MM : Monad M} :
  MonadState ST (StateT ST M).
Proof.
  split.
  exact (λ st : ST, returnM (st, st)).
  exact (λ st : ST, λ _ : ST, returnM (tt, st)).
Defined.

Instance store_optionT `{MM : Monad M} `{MS : MonadState ST M} :
  MonadState ST (optionT M).
Proof. split.
  exact (liftT get).
  exact (λ st : ST, put st ;; returnM (Some tt)).
Defined.

Instance store_optionAT `{MM : Monad M} `{MS : MonadState ST M} :
  MonadState ST (optionAT M).
Proof. split.
  exact (liftT get).
  exact (λ st : ST, put st ;; returnM (SomeA tt)).
Defined.

