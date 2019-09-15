Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Types.Stores.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Result.

Definition ensure_nat (v : cvalue) : State nat :=
  fun st => match v with
            | VNat x => returnR x st
            | _ => crashed 
            end.

Definition plusM (n m : nat) : State nat := returnM (plus n m).

Definition multM (n m : nat) : State nat := returnM (mult n m).

Definition eqbM (n m : nat) : State bool := returnM (Nat.eqb n m).

Definition lebM (n m : nat) : State bool := returnM (Nat.leb n m).

Definition build_natural (n : nat) : State cvalue := 
  returnM (VNat n).

Global Instance nat_numerical : IsNat State cvalue bool nat :=
{
  ensure_nat := ensure_nat;
  build_nat := build_natural;
  extract_nat := fun x => returnM x;
  plus_op := plusM;
  mult_op := multM;
  eq_op := eqbM;
  le_op := lebM;
}.

