Require Import Classes.Except.
Require Import Classes.Joinable.
Require Import Instances.Joinable.
Require Import Types.Stores.
Require Import Types.Result.
Require Import Types.State.
Require Import Instances.Monad.
Require Import Classes.Monad.
Require Import Classes.Applicative.

Definition eval_catch_abstract 
  (st1 st2 : AbstractState unit) : AbstractState unit :=
  bindM (M:=State abstract_store) st1 (fun x => match x with
                                       | JustA _ => st1
                                       | JustOrNoneA _ => st2
                                       | NoneA => st2
                                       end).

Definition fail_abstract : AbstractState unit := 
  pure (F:=State abstract_store) NoneA.

Instance except_abstract : Except AbstractState := 
{
  throw := fail_abstract;
  trycatch := eval_catch_abstract;
}.
