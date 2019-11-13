Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Types.Stores.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Result.
Require Import Instances.Monad.
Require Import Classes.Applicative.

Definition ensure_nat (v : cvalue) : ConcreteState nat :=
  match v with
  | VNat x => liftT (pure x)
  | _ => liftT (pure None)
  end.

Definition extract_natM (n : nat) : ConcreteState nat :=
  liftT (pure n).

Definition plusM (n m : nat) : ConcreteState nat := 
  liftT (pure (plus n m)).

Definition multM (n m : nat) : ConcreteState nat := 
  liftT (pure (mult n m)).

Definition eqbM (n m : nat) : ConcreteState bool := 
  liftT (pure (Nat.eqb n m)).

Definition lebM (n m : nat) : ConcreteState bool := 
  liftT (pure (Nat.leb n m)).

Definition build_natural (n : nat) : ConcreteState cvalue := 
  liftT (pure (VNat n)).

Global Instance nat_numerical : IsNat ConcreteState cvalue bool nat :=
{
  ensure_nat := ensure_nat;
  build_nat := build_natural;
  extract_nat := extract_natM;
  plus_op := plusM;
  mult_op := multM;
  eq_op := eqbM;
  le_op := lebM;
}.

