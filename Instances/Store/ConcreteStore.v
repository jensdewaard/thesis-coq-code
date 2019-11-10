Require Import Types.Maps.
Require Import Types.Stores.
Require Import Language.Statements.
Require Import Classes.Store.
Require Import Types.State.
Require Import Types.Result.
Require Import Types.Stores.
Require Import Instances.Monad.
Require Import Classes.Monad.
Require Import Classes.Applicative.
Require Import Classes.Functor.

Section store_stateT. 
  Context (M : Type -> Type) `{Monad M}.

  Definition stateT_get (S : Type) := fun s : S => pure(s, s).

  Definition stateT_put (S : Type) := fun s : S => fun _ : S => pure(tt, s).

  Global Instance store_stateT (S : Type) : 
  Store S (StateT S M) (inst:=monad_stateT S) :=
  {
    get := @stateT_get S;
    put := @stateT_put S;
  }.
End store_stateT.

Section store_maybeT.
  Context {M : Type -> Type} `{inst : Monad M}.

  Global Instance store_maybeT (S : Type) `{Store S M} :
  Store S (MaybeT M) :=
  {
    get := fmap Just get;
    put := fun s => put s ;; pure (Just tt);
  }.

End store_maybeT.

Section store_maybeAT.
  Context {M : Type -> Type} `{inst : Monad M}.

  Global Instance store_maybeAT (S : Type) `{Store S M} :
  Store S (MaybeAT M) :=
  {
    get := fmap JustA get;
    put := fun s => put s ;; pure (JustA tt);
  }.
End store_maybeAT.
