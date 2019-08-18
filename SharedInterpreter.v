Require Import Statements.
Require Import Monad.
Require Import Classes.IsNat.
Require Import Classes.IsBool.
Require Import Classes.Store.
Require Import Classes.Except.


Definition extract_build_val {M : Type -> Type} {valType boolType natType : Type}
    `{Monad M, IsNat M valType boolType natType, IsBool M valType boolType}
    (v : cvalue) : M valType :=
  match v with
  | VNat n => n' << extract_nat n; build_nat n'
  | VBool b => b' << extract_bool b; build_bool b'
  end.

Fixpoint shared_eval_expr 
    {M : Type -> Type} {valType boolType natType : Type}
    `{Monad M, Store M valType,
      IsNat M valType boolType natType, IsBool M valType boolType}
    (e : expr) : M valType :=
  match e with
  | EVal v =>
      extract_build_val v
  | EVar x =>
      get x
  | EPlus e1 e2 => 
      v1 << shared_eval_expr e1 ;
      v2 << shared_eval_expr e2 ;
      n1 << ensure_nat v1 ;
      n2 << ensure_nat v2 ;
      n << plus_op n1 n2 ;
      build_nat n
  | EMult e1 e2 => 
      v1 << shared_eval_expr e1 ;
      v2 << shared_eval_expr e2 ;
      n1 << ensure_nat v1 ;
      n2 << ensure_nat v2 ;
      n << mult_op n1 n2 ;
      build_nat n
  | EEq e1 e2 =>
      v1 << shared_eval_expr e1 ;
      v2 << shared_eval_expr e2 ;
      n1 << ensure_nat v1 ;
      n2 << ensure_nat v2 ;
      b << eq_op n1 n2 ;
      build_bool b
  | ELe e1 e2 =>
      v1 << shared_eval_expr e1 ;
      v2 << shared_eval_expr e2 ;
      n1 << ensure_nat v1 ;
      n2 << ensure_nat v2 ;
      b << le_op n1 n2;
      build_bool b
  | ENot e1 =>
      v1 << shared_eval_expr e1 ;
      b1 << ensure_bool v1 ;
      b << neg_op b1;
      build_bool b
  | EAnd e1 e2 =>
      v1 << shared_eval_expr e1 ;
      v2 << shared_eval_expr e2 ;
      b1 << ensure_bool v1 ;
      b2 << ensure_bool v2 ;
      b << and_op b1 b2 ;
      build_bool b
  end.

Open Scope com_scope.

Fixpoint shared_ceval 
  {M : Type -> Type} {valType natType boolType : Type}
  `{Monad M, Store M valType, Except M, 
    IsNat M valType boolType natType, IsBool M valType boolType}
  (c : com) : M unit :=
  match c with
  | CSkip => returnM tt
  | c1 ;c; c2 =>
      (shared_ceval c1) ;; (shared_ceval c2)
  | x ::= a => 
      v << shared_eval_expr a ;
      put x v
  | CIf b c1 c2 => 
      v << shared_eval_expr b ;
      b' << ensure_bool v ;
      if_op b' (shared_ceval c1) (shared_ceval c2)
  | try c1 catch c2 => 
      trycatch (shared_ceval c1) (shared_ceval c2)
  | CFail => throw
  end.
