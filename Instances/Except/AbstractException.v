Require Import Classes.Except.
Require Import Classes.Joinable.
Require Import Instances.Joinable.Unit.
Require Import Types.Stores.
Require Import Types.Result.
Require Import Types.State.

Definition eval_catch_abstract {A} `{Joinable A} 
  (st1 st2 : AbstractState A) : AbstractState A :=
  fun st => match (st1 st) with
  | crashedA _ _ => crashedA _ _ 
  | exceptionA _ _ st' => st2 st'
  | exceptionOrReturn _ _ x st' => 
      join_op (exceptionOrReturn _ _ x st') (st2 st')
  | returnRA _ _ x st' => returnRA _ _ x st'
  end.

Definition fail_abstract {A : Type} : AbstractState A :=
  fun st => exceptionA A abstract_store st.

Instance except_abstract : Except AbstractState := 
{
  throw := fail_abstract;
  trycatch := eval_catch_abstract;
}.
