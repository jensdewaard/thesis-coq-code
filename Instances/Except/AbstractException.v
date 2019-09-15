Require Import Classes.Except.
Require Import Classes.Joinable.
Require Import Instances.Joinable.Unit.
Require Import Types.Stores.
Require Import Types.Result.
Require Import Types.State.

Definition eval_catch_abstract {A} `{Joinable A} 
  (st1 st2 : AbstractState A) : AbstractState A :=
  fun st => match (st1 st) with
  | crashedA => crashedA 
  | exceptionA st' => st2 st'
  | exceptionOrReturn x st' => 
      join_op (exceptionOrReturn x st') (st2 st')
  | returnRA x st' => returnRA x st'
  end.

Definition fail_abstract {A : Type} : AbstractState A :=
  fun st => exceptionA st.

Instance except_abstract : Except AbstractState := 
{
  throw := fail_abstract;
  trycatch := eval_catch_abstract;
}.
