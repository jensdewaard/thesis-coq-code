Require Import Classes.IsBool.
Require Import Classes.Monad.
Require Import Language.Statements.
Require Import Types.State.
Require Import Types.Stores.
Require Import Types.Result.
Require Import Instances.Monad.
Require Import Classes.Applicative.

Definition ensure_bool (v : cvalue) : ConcreteState bool :=
  match v with
  | VBool b => liftT (pure b)
  | _ => liftT (pure None)
  end.

Definition build_boolean (b : bool) : ConcreteState cvalue :=
  liftT (pure (VBool b)).

Definition extract_boolean (b : bool) : ConcreteState bool :=
  liftT (pure b).

Definition andbM (b c : bool) : ConcreteState bool := 
  liftT (pure (andb b c)).

Definition negbM (b : bool) : ConcreteState bool := 
  liftT (pure (negb b)).

Definition eval_if {A} (b : bool) (st1 st2 : ConcreteState A) : ConcreteState A :=
  if b then st1 else st2.

Instance boolean_type : IsBool ConcreteState cvalue bool :=
{
  ensure_bool := ensure_bool;
  build_bool := build_boolean;
  extract_bool := extract_boolean;
  and_op := andbM;
  neg_op := negbM;
  if_op := eval_if;
}.
