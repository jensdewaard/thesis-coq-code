Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Result.
Require Import Types.State.

Definition extract_interval (n : nat) : AbstractState interval := 
    returnM (n, n).

Definition ensure_interval (v : avalue) : AbstractState interval :=
  fun st => match v with
            | VInterval i => returnRA i st
            | _ => crashedA
            end.

Definition build_interval (i : interval) : AbstractState avalue :=
  returnM (VInterval i).  

Global Instance isnat_interval : 
  IsNat AbstractState avalue abstr_bool interval := 
{
  extract_nat := extract_interval;
  ensure_nat := ensure_interval;
  build_nat := build_interval;
  plus_op := fun i => fun j => returnM (iplus i j);
  mult_op := fun i => fun j => returnM (imult i j);
  eq_op := fun i => fun j => returnM (ieqb i j);
  le_op := fun i => fun j => returnM (ileqb i j);
}.