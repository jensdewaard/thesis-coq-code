Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import ConcreteInterpreter.
Require Import Instances.Except.AbstractException.
Require Import Instances.Galois.
Require Import Instances.IsBool.AbstractBoolean.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.
Require Import Instances.Preorder.
Require Import Instances.Store.AbstractStore.
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


Lemma abs_trycatch_return : forall c1 c2 ast u a,
  ceval_abstract c1 ast = returnRA u a ->
  ceval_abstract (try c1 catch c2) ast = ceval_abstract c1 ast.
Proof.
  intros c1 c2 ast u a Hceval. 
  unfold ceval_abstract in *. simpl in *.
  unfold eval_catch_abstract. rewrite Hceval.
  reflexivity. 
Qed.


Lemma abs_trycatch_crash : forall c1 c2 ast,
  ceval_abstract c1 ast = crashedA ->
  ceval_abstract (try c1 catch c2) ast = crashedA.
Proof.
  intros c1 c2 ast Hceval. 
  unfold ceval_abstract in *. simpl in *.
  unfold eval_catch_abstract. rewrite Hceval.
  reflexivity. 
Qed.

Lemma abs_trycatch_exception : forall c1 c2 ast ast',
  ceval_abstract c1 ast = exceptionA ast' ->
  ceval_abstract (try c1 catch c2) ast = ceval_abstract c2 ast'.
Proof. 
  intros c1 c2 ast ast' Hceval. unfold ceval_abstract in *. simpl in *.
  unfold eval_catch_abstract. rewrite Hceval. reflexivity.
Qed.

Lemma abs_trycatch_exceptreturn : forall c1 c2 u ast ast',
  ceval_abstract c1 ast = exceptionOrReturn u ast' ->
  ceval_abstract (try c1 catch c2) ast = 
    join_op (exceptionOrReturn tt ast')
            (shared_ceval c2 ast').
Proof. 
  intros c1 c2 u ast ast' Hceval. unfold ceval_abstract in *. simpl in *.
  unfold eval_catch_abstract. rewrite Hceval. reflexivity.
Qed.
