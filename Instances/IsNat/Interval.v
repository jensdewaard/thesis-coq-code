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
    pure_maybeAT _ (pure (n, n)).

Definition ensure_interval (v : avalue) : AbstractState interval :=
  match v with
  | VInterval i => pure_maybeAT _ (pure i)
  | _ => pure NoneA 
  end.

Definition iplusM (i j : interval) : AbstractState interval := 
  pure_maybeAT _ (pure (iplus i j)).
Definition imultM (i j : interval) : AbstractState interval :=
  pure_maybeAT _ (pure (imult i j)).
Definition ieqM (i j : interval) : AbstractState abstr_bool :=
  pure_maybeAT _ (pure (ieqb i j)).
Definition ileM (i j : interval) : AbstractState abstr_bool := 
  pure_maybeAT _ (pure (ileqb i j)).

Definition build_interval (i : interval) : AbstractState avalue :=
  pure_maybeAT _ (pure (VInterval i)).  

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
