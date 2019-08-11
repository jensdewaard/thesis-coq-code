Require Import Types.AbstractBool.
Require Import Classes.BoolType.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Result.
Require Import Types.AbstractStore.

Definition ensure_abool (v : avalue) : AbstractState abstr_bool :=
  fun st => match v with
            | VAbstrBool b => returnRA abstr_bool abstract_store b st
            | _ => crashedA _ _
            end.

Instance abstract_boolean_type : BoolType abstr_bool :=
{
  ensure_boolean := ensure_abool;
  and_op := and_ab;
  neg_op := neg_ab;
}.
