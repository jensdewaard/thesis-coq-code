Require Import Types.State.
Require Import Types.Result.
Require Import Classes.Except.
Require Import Types.Stores.
Require Import Instances.Monad.
Require Import Classes.Monad.
Require Import Classes.Applicative.


Definition eval_catch (st1 st2 : ConcreteState unit) : ConcreteState unit :=
  bindM (M:=State store) st1 (fun m => match m with
                            | Just _ => st1
                            | None => st2
                            end).
                  
Definition fail : ConcreteState unit := pure None.

Instance except_concrete : Except ConcreteState := {
  throw := fail;
  trycatch := eval_catch;
}.
