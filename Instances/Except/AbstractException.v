Require Import Classes.Except.
Require Import Classes.Joinable.
Require Import Instances.Joinable.
Require Import Types.Stores.
Require Import Types.Result.
Require Import Types.State.
Require Import Instances.Monad.

Definition eval_catch_abstract 
  (st1 st2 : AbstractState unit) : AbstractState unit :=
  match st1 with
  | NoneA _ => st2
  | JustA _ st => JustA _ st
  | JustOrNoneA _ st => join_op st1 st2
  end.

Definition fail_abstract : AbstractState unit := NoneA _.

Instance except_abstract : Except AbstractState := 
{
  throw := fail_abstract;
  trycatch := eval_catch_abstract;
}.
