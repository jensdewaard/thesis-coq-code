Require Import Classes.IsBool.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Language.Statements.
Require Import Types.Stores.
Require Import Instances.Monad.

Generalizable Variable M.

Definition ensure_bool `{M_monad : MonadFail M} (v : cvalue) : M bool :=
  match v with
  | VBool b => returnM b
  | _ => fail
  end.

Definition build_boolean `{M_monad : Monad M} (b : bool) : M cvalue :=
  returnM (VBool b).

Definition extract_boolean `{M_monad : Monad M} (b : bool) : M bool :=
  returnM b.

Definition andbM `{M_monad : Monad M} (b c : bool) : M bool := 
  returnM (andb b c).

Definition negbM `{M_monad : Monad M} (b : bool) : M bool := 
  returnM (negb b).

Definition eval_if {A} `{M_monad : Monad M} (b : bool) (st1 st2 : M A) : M A :=
  if b then st1 else st2.

Instance boolean_type `{M_fail : MonadFail M} : IsBool M cvalue bool :=
{
  ensure_bool := ensure_bool;
  build_bool := build_boolean;
  extract_bool := extract_boolean;
  and_op := andbM;
  neg_op := negbM;
  if_op := eval_if;
}.
