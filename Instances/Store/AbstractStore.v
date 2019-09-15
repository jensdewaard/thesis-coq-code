Require Export Coq.Strings.String.
Require Import Classes.Store.
Require Import Language.Statements.
Require Import Types.Maps.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

Definition abstract_store_top : abstract_store :=
  fun _ => VTop.
Definition abstract_store_bottom : abstract_store :=
  fun _ => VBottom.
Definition abstract_store_join
    (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => VTop.

Definition abstract_store_get (x : string) : 
  AbstractState avalue := 
  fun st => returnRA (st x) st.

Definition abstract_store_put 
  (x : string) (v : avalue) : 
  AbstractState unit :=
  fun st => returnRA tt (t_update st x v).

Instance store_abstract : Store AbstractState avalue := {
  get := abstract_store_get;
  put := abstract_store_put;
}.
