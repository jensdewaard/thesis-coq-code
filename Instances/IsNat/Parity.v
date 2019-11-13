Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Types.Parity.
Require Import Types.AbstractBool.
Require Import Language.Statements.
Require Import Types.Result.
Require Import Types.Stores.
Require Import Types.State.
Require Import Instances.Monad.
Require Import Types.Maps.
Require Import Classes.Applicative.
Require Import Instances.Monad.

Print AbstractState.
Print liftT.
Definition ensure_par (v : avalue) : AbstractState parity :=
  match v with
  | VParity x => liftT (liftT (pure x))
  | _ => liftT (liftT (pure NoneA))
  end.

Fixpoint extract_par (n : nat) : parity :=
  match n with 
  | 0 => par_even
  | S 0 => par_odd
  | S (S n) => extract_par n
end.

Definition extract_parM (n : nat) : AbstractState parity :=
  pure_maybeAT _ (pure_state (extract_par n)).

Definition pplusM (n m : parity) : AbstractState parity :=
  pure_maybeAT _ (pure (parity_plus n m)).

Definition pmultM (n m : parity) : AbstractState parity :=
  pure_maybeAT _ (pure (parity_mult n m)).

Definition peqM (n m : parity) : AbstractState abstr_bool :=
  pure_maybeAT _ (pure (parity_eq n m)).

Definition pleM (n m : parity) : AbstractState abstr_bool :=
  pure_maybeAT _ (pure ab_top).

Definition build_parity (p : parity) : AbstractState avalue :=
  pure_maybeAT _ (pure (VParity p)).

Global Instance isnat_parity : 
  IsNat AbstractState avalue abstr_bool parity :=
{
  ensure_nat := ensure_par;
  extract_nat := extract_parM;
  build_nat := build_parity;
  plus_op := pplusM;
  mult_op := pmultM;
  eq_op := peqM;
  le_op := pleM;
}.

