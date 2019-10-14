Require Import Classes.IsBool.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Instances.Except.AbstractException.
Require Import Instances.Joinable.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

Definition ensure_abool (v : avalue) : AbstractState abstr_bool :=
  fun st => match v with
            | VAbstrBool b => returnRA b st
            | _ => crashedA
            end.

Definition and_abM (b c : abstr_bool) := returnM (and_ab b c).
Definition neg_abM (b : abstr_bool) := returnM (neg_ab b).

Definition eval_if_abstract {A} `{Joinable A} 
  (b : abstr_bool) (st1 st2 : AbstractState A) 
  : AbstractState A :=
  match b with
  | ab_true   => st1
  | ab_false  => st2
  | ab_top    => join_op st1 st2
  | ab_bottom => fail_abstract
  end.

Definition extract_ab (b : bool) : abstr_bool := 
  match b with
  | true => ab_true
  | false => ab_false
  end.

Definition extract_abM (b : bool) : AbstractState abstr_bool :=
  returnM (extract_ab b).

Definition build_abool (b : abstr_bool) : AbstractState avalue :=
  returnM (VAbstrBool b).

Instance abstract_boolean_type : IsBool AbstractState avalue abstr_bool :=
{
  ensure_bool := ensure_abool;
  extract_bool := extract_abM;
  build_bool := build_abool;
  and_op := and_abM;
  neg_op := neg_abM;
  if_op := eval_if_abstract;
}.
