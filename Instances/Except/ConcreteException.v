Require Import Types.State.
Require Import Types.Result.
Require Import Classes.Except.
Require Import Types.Stores.
Require Import Instances.Monad.

Definition eval_catch (st1 st2 : State unit) : State unit :=
  match st1 with
  | None _ => st2
  | Just _ x => st1
  end.

Definition fail : State unit := None _.

Instance except_concrete : Except State := {
  throw := fail;
  trycatch := eval_catch;
}.
