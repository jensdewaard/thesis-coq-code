Require Import Classes.IsBool.
Require Import Classes.Monad.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Stores.
Require Import Types.Result.
Require Import Instances.Monad.

Definition ensure_bool (v : cvalue) : State bool :=
  match v with
  | VBool b => Just _ (returnM b)
  | _ => None _
  end.

Definition build_boolean (b : bool) : State cvalue :=
  Just _ (returnM (VBool b)).

Definition extract_boolean (b : bool) : State bool :=
  Just _ (returnM b).

Definition andbM (b c : bool) : State bool := 
  Just _ (returnM (andb b c)).

Definition negbM (b : bool) : State bool := 
  Just _ (returnM (negb b)).

Definition eval_if {A} (b : bool) (st1 st2 : State A) : State A :=
  if b then st1 else st2.


Instance boolean_type : IsBool State cvalue bool :=
{
  ensure_bool := ensure_bool;
  build_bool := build_boolean;
  extract_bool := extract_boolean;
  and_op := andbM;
  neg_op := negbM;
  if_op := eval_if;
}.
