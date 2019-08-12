Require Import Classes.BoolType.
Require Import Classes.Numerical.
Require Import Classes.Monad.
Require Import ConcreteInterpreter.
Require Import Instances.BoolType.AbstractBoolean.
Require Import Instances.Galois.Parity.
Require Import Instances.Joinable.Unit.
Require Import Instances.Numerical.Parity.
Require Import Instances.Preorder.Unit.
Require Import Joinable.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.AbstractStore.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.Result.
Require Import Types.State.

Open Scope com_scope.

(*Definition abstract_aexp := shared_aexp 
  parity 
  extract_par 
  parity_plus 
  parity_mult
  abstract_store
  get_abstract.*)

  
Definition extract (v : cvalue) : avalue :=
  match v with
  | VNat x => VParity (extract_par x)
  | VBool x => VAbstrBool (extract_bool x)
  end.
  
Fixpoint eval_expr_abstract (e : expr) : AbstractState avalue :=
  match e with
  | EVal x => returnM (extract x)
  | EVar x => st << get_abstract ;
      returnM (st x)
  | EPlus e1 e2 => 
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      n1 << (ensure_numerical v1) ;
      n2 << (ensure_numerical v2) ;
      returnM (VParity (plus_op n1 n2))
  | EMult e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      n1 << (ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (VParity (mult_op n1 n2))
  | EEq e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      n1 << (ensure_numerical v1) ;
      n2 << (ensure_numerical v2) ;
      returnM (VAbstrBool (eq_op n1 n2))
  | ELe e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      n1 << (ensure_numerical v1) ;
      n2 << (ensure_numerical v2) ;
      returnM (VAbstrBool (le_op n1 n2))
  | ENot e =>
      v << (eval_expr_abstract e) ;
      b << (ensure_boolean v) ;
      returnM (VAbstrBool (neg_op b))
  | EAnd e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      b1 << (ensure_boolean v1) ;
      b2 << (ensure_boolean v2) ;
      returnM (VAbstrBool (and_op b1 b2))
  end.

Definition eval_if_abstract {A} `{Joinable A} 
  (b : abstr_bool) (st1 st2 : AbstractState A) 
  : AbstractState A :=
  match b with
  | ab_true   => st1
  | ab_false  => st2
  | ab_top    => join_op st1 st2
  | ab_bottom => fail_abstract
  end.
  
Definition eval_catch_abstract {A} `{Joinable A} 
  (st1 st2 : AbstractState A) : AbstractState A :=
  fun st => match (st1 st) with
  | crashedA _ _ => crashedA _ _ 
  | exceptionA _ _ st' => st2 st'
  | exceptionOrReturn _ _ x st' => 
      join_op (exceptionOrReturn _ _ x st') (st2 st')
  | returnRA _ _ x st' => returnRA _ _ x st'
  end.

Fixpoint ceval_abstract (c : com) : AbstractState unit :=
  match c with
  | CSkip => returnM tt
  | c1 ;c; c2 =>
      (ceval_abstract c1) ;; (ceval_abstract c2)
  | x ::= a => 
      p << (eval_expr_abstract a) ;
      st << get_abstract ;
      put_abstract (t_update st x p)
  | CIf b c1 c2 => 
      v << (eval_expr_abstract b) ;
      b' << (ensure_boolean v) ;
      eval_if_abstract b' (ceval_abstract c1) (ceval_abstract c2)
  | try c1 catch c2 => 
      eval_catch_abstract (ceval_abstract c1) (ceval_abstract c2)
  | CFail => fail_abstract
  end.
