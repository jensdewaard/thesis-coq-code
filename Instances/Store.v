Require Export Base.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadState.
Require Import Instances.Monad.
Require Import Language.Statements.
Require Import Types.Maps.
Require Import Types.State.
Require Import Types.Stores.
Require Import Classes.Joinable.

Section store_state.
  Context {S : Type} `{!Inhabited S} `{Joinable S}.
  Definition state_get := λ s : S, (s, s).
  Definition state_put := λ s : S, λ _ : S, (tt, s).

  Global Instance store_state : MonadState S (State S) :=
  {
    get := state_get;
    put := state_put;
  }.
End store_state.

Section store_stateT.
  Context (M : Type -> Type) `{M_monad : Monad M}.
  Context {S : Type} `{!Inhabited S} `{Joinable S}.

  Definition stateT_get := fun s : S => returnM (s, s).

  Definition stateT_put := fun s : S => fun _ : S => returnM (tt, s).

  Global Instance store_stateT : 
  MonadState S (StateT _ M) :=
  {
    get := stateT_get;
    put := stateT_put;
  }.
End store_stateT.

Section store_optionT.
  Context {M : Type -> Type} `{M_monad : Monad M}.

  Global Instance store_optionT (S : Type) `{MonadState S M} :
  MonadState S (optionT M) :=
  {
    get := liftT get;
    put := fun s => put s ;; returnM (Some tt);
  }.
End store_optionT.

Section store_optionAT.
  Context {M : Type -> Type} `{M_monad : Monad M}.

  Global Instance store_optionAT (S : Type) `{MonadState S M} :
  MonadState S (optionAT M) :=
  {
    get := liftT get;
    put := fun s => put s ;; returnM (SomeA tt);
  }.
End store_optionAT.

