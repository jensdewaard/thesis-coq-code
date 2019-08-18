Require Import Coq.Arith.Arith.
Require Import Utf8.

Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Instances.Except.ConcreteException.
Require Import Instances.IsBool.Boolean.
Require Import Instances.IsNat.Nat.
Require Import Instances.Store.ConcreteStore.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.Maps.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

Open Scope com_scope.

(*Definition concrete_aexp := shared_aexp 
  nat 
  (fun x => x) 
  plus 
  mult 
  store
  get.*)
  
Fixpoint eval_expr (e : expr) : State cvalue :=
  shared_eval_expr e.

Fixpoint ceval (c : com) : State unit :=
  shared_ceval c.
