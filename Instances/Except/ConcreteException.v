Require Import Types.State.
Require Import Types.Result.
Require Import Classes.Except.
Require Import Types.Stores.

Definition eval_catch (st1 st2 : State unit) : State unit :=
  fun st => match (st1 st) with
  | crashed => crashed 
  | exception st' => (st2 st')
  | x => x
  end.

Definition fail : State unit :=
  fun st => exception st.

Instance except_concrete : Except State := {
  throw := fail;
  trycatch := eval_catch;
}.
