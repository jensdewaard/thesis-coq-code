Require Import Types.Maps.
Require Import Types.Stores.
Require Import Language.Statements.
Require Import Classes.Store.
Require Import Types.Stores.
Require Import Types.State.
Require Import Classes.Monad.
Require Import Instances.Monad.
Require Import Types.Maybe.

Section store_stateT_concrete. 
  Context (M : Type -> Type) `{M_monad : Monad M}.

  Definition stateT_get := fun s : store => returnM (s, s).

  Definition stateT_put := fun s : store => fun _ : store => returnM (tt, s).

  Definition retrieve_concrete (x : string) : StateT store M cvalue :=
    fun s : store => returnM (s x, s).

  Definition update_concrete (x : string) (v : cvalue) : StateT store M store :=
    fun s : store => let s' := t_update s x v in returnM (s', s').

  Global Instance store_stateT : 
  Store store (StateT store M) cvalue :=
  {
    get := stateT_get;
    put := stateT_put;
    retrieve := retrieve_concrete;
    update := update_concrete;
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
    Store abstract_store (StateT abstract_store M) avalue :=
  {
    get := get_abstract;
    put := put_abstract;
    retrieve := retrieve_abstract;
    update := update_abstract;
  }.
End store_stateT_abstract.


Section store_maybeT.
  Context {M : Type -> Type} `{M_monad : Monad M} {V : Type}.

  Global Instance store_maybeT (S : Type) `{Store S M V} :
  Store S (MaybeT M) V :=
  {
    get := liftT get;
    put := fun s => put s ;; returnM (Just tt);
    retrieve := fun x : string => liftT (retrieve x);
    update := fun x v => liftT (update x v);
  }.
End store_maybeT.

Section store_maybeAT.
  Context {M : Type -> Type} `{M_monad : Monad M} {V : Type}.

  Global Instance store_maybeAT (S : Type) `{Store S M V} :
  Store S (MaybeAT M) V :=
  {
    get := liftT get;
    put := fun s => put s ;; returnM (JustA tt);
    retrieve := fun x => liftT (retrieve x);
    update := fun x v => liftT (update x v);
  }.
End store_maybeAT.

