Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Types.Stores.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Result.
Require Import Instances.Monad.

Definition ensure_nat (v : cvalue) : State nat :=
  match v with
  | VNat x => Just _ (return_state x)
  | _ => None _
  end.

Definition extract_natM (n : nat) : State nat :=
  Just _ (return_state n).

Definition plusM (n m : nat) : State nat := Just _ (returnM (plus n m)).

Definition multM (n m : nat) : State nat := Just _ (returnM (mult n m)).

Definition eqbM (n m : nat) : State bool := Just _ (returnM (Nat.eqb n m)).

Definition lebM (n m : nat) : State bool := Just _ (returnM (Nat.leb n m)).

Definition build_natural (n : nat) : State cvalue := 
  Just _ (returnM (VNat n)).

Global Instance nat_numerical : IsNat State cvalue bool nat :=
{
  ensure_nat := ensure_nat;
  build_nat := build_natural;
  extract_nat := extract_natM;
  plus_op := plusM;
  mult_op := multM;
  eq_op := eqbM;
  le_op := lebM;
}.

