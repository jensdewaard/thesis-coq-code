Require Import Classes.BoolType.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.AbstractStore.
Require Import Types.Result.

Definition ensure_bool (v : cvalue) : State bool :=
  fun st => match v with
            | VBool b => returnR bool store b st
            | _ => crashed _ _
            end.
  
Instance boolean_type : BoolType bool :=
{
  ensure_boolean := ensure_bool;
  and_op := andb;
  neg_op := negb;
}.
