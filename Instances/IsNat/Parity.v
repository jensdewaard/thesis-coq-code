Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Types.Parity.
Require Import Types.AbstractBool.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Result.
Require Import Types.Stores.

Definition ensure_par (v : avalue) : AbstractState parity :=
  fun st => match v with
            | VParity x => returnRA parity abstract_store x st
            | _ => crashedA _ _
            end.

Fixpoint extract_par (n : nat) : parity :=
  match n with 
  | 0 => par_even
  | S 0 => par_odd
  | S (S n) => extract_par n
end.

Definition extract_parM (n : nat) : AbstractState parity :=
  returnM (extract_par n).

Definition pplusM (n m : parity) : AbstractState parity :=
  returnM (parity_plus n m).

Definition pmultM (n m : parity) : AbstractState parity :=
  returnM (parity_mult n m).

Definition peqM (n m : parity) : AbstractState abstr_bool :=
  returnM (parity_eq n m).

Definition pleM (n m : parity) : AbstractState abstr_bool :=
  returnM ab_top.

Definition build_parity (p : parity) : AbstractState avalue :=
  returnM (VParity p).

Global Instance parity_numerical : 
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

