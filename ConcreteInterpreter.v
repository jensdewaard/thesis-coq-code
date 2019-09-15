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
  
Definition eval_expr (e : expr) : State cvalue :=
  shared_eval_expr e.

Definition ceval (c : com) : State unit :=
  shared_ceval c.

Lemma trycatch_return : forall c1 c2 st u st',
  ceval c1 st = Result.returnR u st' ->
  ceval (try c1 catch c2) st = ceval c1 st.
Proof.
  intros c1 c2 st u st' Hceval. 
  unfold ceval in *. simpl in *.
  unfold eval_catch. rewrite Hceval.
  reflexivity. 
Qed.

Lemma trycatch_exception : forall c1 c2 st st',
  ceval c1 st = Result.exception st' ->
  ceval (try c1 catch c2) st = ceval c2 st'.
Proof.
  intros c1 c2 st st' Hceval. 
  unfold ceval in *. simpl in *.
  unfold eval_catch. rewrite Hceval.
  reflexivity. 
Qed.
