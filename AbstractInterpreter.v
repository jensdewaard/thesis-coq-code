Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import ConcreteInterpreter.
Require Import Instances.Except.AbstractException.
Require Import Instances.Galois.Parity.
Require Import Instances.IsBool.AbstractBoolean.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.Unit.
Require Import Instances.Preorder.Unit.
Require Import Instances.Store.AbstractStore.
Require Import Joinable.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

Open Scope com_scope.
  
Definition eval_expr_abstract (e : expr) : AbstractState avalue :=
  shared_eval_expr e.
  

Definition ceval_abstract (c : com) : AbstractState unit :=
  shared_ceval c.
