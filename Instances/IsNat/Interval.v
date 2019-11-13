Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Result.
Require Import Types.State.
Require Import Instances.Monad.
Require Import Classes.Applicative.

Definition extract_interval (n : nat) : AbstractState interval := 
  liftT (pure (n, n)).

Definition ensure_interval (v : avalue) : AbstractState interval :=
  match v with
  | VInterval i => liftT (pure i)
  | _ => liftT (pure NoneA)
  end.

Definition iplusM (i j : interval) : AbstractState interval := 
  liftT (pure (iplus i j)).
Definition imultM (i j : interval) : AbstractState interval :=
  liftT (pure (imult i j)).
Definition ieqM (i j : interval) : AbstractState abstr_bool :=
  liftT (pure (ieqb i j)).
Definition ileM (i j : interval) : AbstractState abstr_bool := 
  liftT (pure (ileqb i j)).

Definition build_interval (i : interval) : AbstractState avalue :=
  liftT (pure (VInterval i)).  

Global Instance isnat_interval : 
  IsNat AbstractState avalue abstr_bool interval := 
{
  extract_nat := extract_interval;
  ensure_nat := ensure_interval;
  build_nat := build_interval;
  plus_op := iplusM;
  mult_op := imultM;
  eq_op := ieqM;
  le_op := ileM;
}.
