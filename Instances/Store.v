Require Import Classes.Monad.
Require Import Classes.Monad.MonadState.
Require Import Instances.Monad.
Require Import Language.Statements.
Require Import Types.Maps.
Require Import Types.Maybe.
Require Import Types.State.
Require Import Types.Stores.

Section store_stateT_concrete. 
  Context (M : Type -> Type) `{M_monad : Monad M}.

  Definition stateT_get := fun s : store => returnM (s, s).

  Definition stateT_put := fun s : store => fun _ : store => returnM (tt, s).

  Definition retrieve_concrete (x : string) : StateT store M cvalue :=
    fun s : store => returnM (s x, s).

  Definition update_concrete (x : string) (v : cvalue) : StateT store M store :=
    fun s : store => let s' := t_update s x v in returnM (s', s').

  Global Instance store_stateT : 
  MonadState store (StateT store M) :=
  {
    get := stateT_get;
    put := stateT_put;
  }.
End store_stateT_concrete.

Section store_stateT_abstract.
  Context (M : Type -> Type) `{M_monad : Monad M}.

  Definition get_abstract := fun s : abstract_store => returnM (s, s).
  Definition put_abstract := fun s : abstract_store => 
    fun _ : abstract_store => returnM (tt, s).
  Definition retrieve_abstract (x : string) : StateT abstract_store M avalue :=
    fun s : abstract_store => returnM (s x, s).
  Definition update_abstract (x : string) (v : avalue) : 
    StateT abstract_store M abstract_store :=
    fun s : abstract_store => let s' := t_update s x v in returnM (s', s').

  Global Instance store_stateT_abstract : 
    MonadState abstract_store (StateT abstract_store M) :=
  {
    get := get_abstract;
    put := put_abstract;
  }.
End store_stateT_abstract.

Section store_maybeT.
  Context {M : Type -> Type} `{M_monad : Monad M}.

  Global Instance store_maybeT (S : Type) `{MonadState S M} :
  MonadState S (MaybeT M) :=
  {
    get := liftT get;
    put := fun s => put s ;; returnM (Just tt);
  }.
End store_maybeT.

Section store_maybeAT.
  Context {M : Type -> Type} `{M_monad : Monad M}.

  Global Instance store_maybeAT (S : Type) `{MonadState S M} :
  MonadState S (MaybeAT M) :=
  {
    get := liftT get;
    put := fun s => put s ;; returnM (JustA tt);
  }.
End store_maybeAT.

