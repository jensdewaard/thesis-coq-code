Require Import Classes.IsBool.
Require Import Classes.Monad.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Stores.
Require Import Types.Result.

Definition ensure_bool (v : cvalue) : State bool :=
  fun st => match v with
            | VBool b => returnR bool store b st
            | _ => crashed _ _
            end.

Definition build_boolean (b : bool) : State cvalue :=
  returnM (VBool b).

Definition extract_boolean (b : bool) : State bool :=
  returnM b.

Definition andbM (b c : bool) : State bool := returnM (andb b c).

Definition negbM (b : bool) : State bool := returnM (negb b).

Definition eval_if {A} (b : bool) (st1 st2 : State A) : State A :=
  if b then st1 else st2.

Instance boolean_type : IsBool State cvalue bool :=
{
  ensure_bool := ensure_bool;
  extract_bool := extract_boolean;
  build_bool := build_boolean;
  and_op := andbM;
  neg_op := negbM;
  if_op := eval_if;
}.
