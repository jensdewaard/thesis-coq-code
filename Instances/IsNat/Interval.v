Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Instances.Monad.
Require Import Classes.Applicative.

Implicit Type M : Type → Type.
Generalizable Variable M.

Definition extract_interval `{M_monad : Monad M} (n : nat) : M interval := 
  pure (n, n).

Definition ensure_interval `{M_fail : MonadFail M} (v : avalue) : M interval :=
  match v with
  | VInterval i => pure i
  | _ => fail
  end.

Definition iplusM `{M_monad : Monad M} (i j : interval) : M interval := 
  pure (iplus i j).

Definition imultM `{M_monad : Monad M} (i j : interval) : M interval :=
  pure (imult i j).

Definition ieqM `{M_monad : Monad M} (i j : interval) : M abstr_bool :=
  pure (ieqb i j).

Definition ileM `{M_monad : Monad M} (i j : interval) : M abstr_bool := 
  pure (ileqb i j).

Definition build_interval `{M_monad : Monad M} (i : interval) : M avalue :=
  pure (VInterval i).  

Global Instance isnat_interval `{M_fail : MonadFail M} :
  IsNat M avalue abstr_bool interval :=
{
  extract_nat := extract_interval;
  ensure_nat := ensure_interval;
  build_nat := build_interval;
  plus_op := iplusM;
  mult_op := imultM;
  eq_op := ieqM;
  le_op := ileM;
}.
