Require Import Classes.Numerical.
Require Import Types.Parity.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Result.
Require Import Types.AbstractStore.

Definition ensure_par (v : avalue) : AbstractState parity :=
  fun st => match v with
            | VParity x => returnRA parity abstract_store x st
            | _ => crashedA _ _
            end.

Global Instance parity_numerical : Numerical parity :=
{
  ensure_numerical := ensure_par;
  plus_op := parity_plus;
  mult_op := parity_mult;
  eq_op := parity_eq;
  le_op := parity_leb;
}.

