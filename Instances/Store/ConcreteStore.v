Require Import Types.Maps.
Require Import Language.Statements.
Require Import Classes.Store.
Require Import Types.State.
Require Import Types.Result.
Require Import Types.Stores.

Definition store_get (x : string) : State cvalue := fun st =>
  returnR cvalue store (st x) st.

Definition store_put (x : string) (v : cvalue) : State unit := 
  fun st => returnR unit store tt (t_update st x v).

Check store_put.
Check put.

Instance store_concrete : Store State cvalue := {
  get := store_get;
  put := store_put;
}.
