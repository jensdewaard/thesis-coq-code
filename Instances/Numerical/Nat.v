Require Import Classes.Numerical.
Require Import Types.AbstractStore.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Result.

Definition ensure_nat (v : cvalue) : State nat :=
  fun st => match v with
            | VNat x => returnR nat store x st
            | _ => crashed _ _
            end.

Global Instance nat_numerical : Numerical nat :=
{
  ensure_numerical := ensure_nat;
  plus_op := plus;
  mult_op := mult;
  eq_op := Nat.eqb;
  le_op := Nat.leb;
}.

