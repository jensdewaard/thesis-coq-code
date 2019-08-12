Require Import Coq.Arith.Arith.
Require Import Utf8.

Require Import Classes.Monad.
Require Import Instances.BoolType.Boolean.
Require Import Instances.Numerical.Nat.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.AbstractStore.
Require Import Types.Maps.
Require Import Types.Result.
Require Import Types.State.

Open Scope com_scope.

(*Definition concrete_aexp := shared_aexp 
  nat 
  (fun x => x) 
  plus 
  mult 
  store
  get.*)
  
Fixpoint eval_expr (e : expr) : State cvalue :=
  match e with
  | EVal x => returnM x
  | EVar x => st << get ;
      returnM (st x)
  | EPlus e1 e2 => 
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (VNat (Numerical.plus_op n1 n2))
  | EMult e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (VNat (Numerical.mult_op n1 n2))
  | EEq e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (VBool (Numerical.eq_op n1 n2))
  | ELe e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (VBool (Numerical.le_op n1 n2))
  | ENot e =>
      v << (eval_expr e) ;
      b << (BoolType.ensure_boolean v) ;
      returnM (VBool (BoolType.neg_op b))
  | EAnd e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      b1 << (BoolType.ensure_boolean v1) ;
      b2 << (BoolType.ensure_boolean v2) ;
      returnM (VBool (BoolType.and_op b1 b2))
  end.

Definition eval_if {A} (b : bool) (st1 st2 : State A) : State A :=
  if b then st1 else st2.

Definition eval_catch {A} (st1 st2 : State A) : State A :=
  fun st => match (st1 st) with
  | crashed _ _ => crashed _ _
  | exception _ _ st' => (st2 st')
  | x => x
  end.

Fixpoint ceval (c : com) : State unit :=
  match c with
  | CSkip => returnM tt
  | c1 ;c; c2 => 
      (ceval c1) ;; (ceval c2)
  | x ::= a => 
      n << (eval_expr a) ;
      st << get ;
      put (t_update st x n)
  | CIf b c1 c2 => 
      v << (eval_expr b) ;
      b' << (ensure_bool v) ;
      eval_if b' (ceval c1) (ceval c2)
  | try c1 catch c2 => eval_catch (ceval c1) (ceval c2)
  | CFail => fail
  end.
