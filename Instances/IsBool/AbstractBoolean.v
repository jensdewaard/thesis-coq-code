Require Import Classes.Applicative.
Require Import Classes.IsBool.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Instances.Except.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Stores.

Generalizable Variable M.

Definition ensure_abool `{M_fail : MonadFail M} (v : avalue) : M abstr_bool :=
  match v with
  | VAbstrBool b => pure b
  | _ => fail
  end.

Definition and_abM `{M_monad : Monad M} (b c : abstr_bool) : M abstr_bool := 
  pure (and_ab b c).

Definition neg_abM `{M_monad : Monad M} (b : abstr_bool) : M abstr_bool := 
  pure (neg_ab b).

Definition eval_if_abstract `{M_fail : MonadFail M} `{M_joinable : Joinable (M (unit))}
  (b : abstr_bool) (st1 st2 : M unit) 
  : M unit := 
  match b with
  | ab_true   => st1
  | ab_false  => st2
  | ab_top    => join_op st1 st2
  | ab_bottom => fail
  end.

Definition extract_ab (b : bool) : abstr_bool := 
  match b with
  | true => ab_true
  | false => ab_false
  end.

Definition extract_abM `{M_monad : Monad M} (b : bool) : M abstr_bool :=
  pure (extract_ab b).

Definition build_abool `{M_monad : Monad M} (b : abstr_bool) : M avalue :=
  pure (VAbstrBool b).

Instance abstract_boolean_type `{M_fail : MonadFail M} `{M_joinable : Joinable (M (unit))} : 
IsBool M avalue abstr_bool :=
{
  ensure_bool := ensure_abool;
  extract_bool := extract_abM;
  build_bool := build_abool;
  and_op := and_abM;
  neg_op := neg_abM;
  if_op := eval_if_abstract;
}.
