Require Import Types.State.
Require Import Types.Result.
Require Import Classes.Except.
Require Import Types.Stores.

Definition eval_catch {A} (st1 st2 : State A) : State A :=
  fun st => match (st1 st) with
  | crashed => crashed 
  | exception st' => (st2 st')
  | x => x
  end.

Definition fail {A : Type} : State A :=
  fun st => exception st.

Instance except_concrete : Except State := {
  throw := fail;
  trycatch := eval_catch;
}.
