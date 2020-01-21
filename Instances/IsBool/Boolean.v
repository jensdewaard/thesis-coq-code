Require Import Classes.IsBool.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Language.Statements.
Require Import Types.Stores.
Require Import Instances.Monad.
Require Import Classes.Applicative.

Generalizable Variable M.

Definition ensure_bool `{MonadFail M} (v : cvalue) : M bool :=
  match v with
  | VBool b => pure b
  | _ => fail
  end.

Definition build_boolean `{Monad M} (b : bool) : M cvalue :=
  pure (VBool b).

Definition extract_boolean `{Monad M} (b : bool) : M bool :=
  pure b.

Definition andbM `{Monad M} (b c : bool) : M bool := 
  pure (andb b c).

Definition negbM `{Monad M} (b : bool) : M bool := 
  pure (negb b).

Definition eval_if {A} `{Monad M} (b : bool) (st1 st2 : M A) : M A :=
  if b then st1 else st2.

Instance boolean_type `{MonadFail M} : IsBool M cvalue bool :=
{
  ensure_bool := ensure_bool;
  build_bool := build_boolean;
  extract_bool := extract_boolean;
  and_op := andbM;
  neg_op := negbM;
  if_op := eval_if;
}.
