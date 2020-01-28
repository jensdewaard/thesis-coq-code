Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Types.Stores.
Require Import Language.Statements.
Require Import Instances.Monad.
Require Import Classes.Applicative.

Implicit Type M : Type → Type.
Generalizable Variable M.

Definition ensure_nat `{M_fail : MonadFail M} (v : cvalue) : M nat :=
  match v with
  | VNat x => pure x
  | _ => fail
  end.

Definition extract_natM `{M_monad : Monad M} (n : nat) : M nat :=
  pure n.

Definition plusM `{M_monad : Monad M} (n m : nat) : M nat := 
  pure (plus n m).

Definition multM `{M_monad : Monad M} (n m : nat) : M nat := 
  pure (mult n m).

Definition eqbM `{M_monad : Monad M} (n m : nat) : M bool := 
  pure (Nat.eqb n m).

Definition lebM `{M_monad : Monad M} (n m : nat) : M bool := 
  pure (Nat.leb n m).

Definition build_natural `{M_monad : Monad M} (n : nat) : M cvalue := 
  pure (VNat n).

Global Instance nat_numerical `{M_fail : MonadFail M} : IsNat M cvalue bool nat :=
{
  ensure_nat := ensure_nat;
  build_nat := build_natural;
  extract_nat := extract_natM;
  plus_op := plusM;
  mult_op := multM;
  eq_op := eqbM;
  le_op := lebM;
}.
