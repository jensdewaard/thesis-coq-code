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

Section store_stateT_concrete. 
  Context (M : Type -> Type) `{Monad M, Applicative M}.

  Definition stateT_get (S : Type) := fun s : S => pure (s, s).

  Definition stateT_put (S : Type) := fun s : S => fun _ : S => pure (tt, s).

  Definition retrieve_concrete (x : string) : StateT store M cvalue :=
    fun s : store => pure(s x, s).

  Definition update_concrete (x : string) (v : cvalue) : StateT store M store :=
    fun s : store => let s' := t_update s x v in pure(s', s').

  Global Instance store_stateT (S : Type) : 
  Store store (StateT store M) cvalue :=
  {
    get := stateT_get store;
    put := stateT_put store;
    retrieve := retrieve_concrete;
    update := update_concrete;
  }.
End store_stateT_concrete.

Section store_stateT_abstract.
  Context (M : Type -> Type) `{Monad M, Applicative M}.

  Definition get_abstract (S : Type) := fun s : S => pure (s, s).
  Definition put_abstract (S : Type) := fun s : S => fun _ : S => pure (tt, s).
  Definition retrieve_abstract (x : string) : StateT abstract_store M avalue :=
    fun s : abstract_store => pure (s x, s).
  Definition update_abstract (x : string) (v : avalue) : 
    StateT abstract_store M abstract_store :=
    fun s : abstract_store => let s' := t_update s x v in pure(s', s').

  Global Instance store_stateT_abstract (S : Type) : 
    Store abstract_store (StateT abstract_store M) avalue :=
  {
    get := get_abstract abstract_store;
    put := put_abstract abstract_store;
    retrieve := retrieve_abstract;
    update := update_abstract;
  }.
End store_stateT_abstract.


Section store_maybeT.
  Context {M : Type -> Type} `{inst : Monad M} {V : Type}.

  Global Instance store_maybeT (S : Type) `{Store S M V} :
  Store S (MaybeT M) V :=
  {
    get := liftT get;
    put := fun s => put s ;; pure (Just tt);
    retrieve := fun x : string => liftT (retrieve x);
    update := fun x v => liftT (update x v);
  }.
End store_maybeT.

Section store_maybeAT.
  Context {M : Type -> Type} `{inst : Monad M} {V : Type}.

  Global Instance store_maybeAT (S : Type) `{Store S M V} :
  Store S (MaybeAT M) V :=
  {
    get := fmap JustA get;
    put := fun s => put s ;; pure (JustA tt);
    retrieve := fun x => liftT (retrieve x);
    update := fun x v => liftT (update x v);
  }.
End store_maybeAT.
