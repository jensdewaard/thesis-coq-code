Require Import Statements.
Require Import Monad.
Require Import Classes.Numerical.
Require Import Classes.BoolType.
Require Import Instances.Numerical.Nat.
Require Import Instances.BoolType.Boolean.

About nat_numerical.

Fail Fixpoint shared_eval_expr 
  {state_type : Type -> Type} 
  `{Monad state_type}
  {value : Type}
  {extract : cvalue -> value}
  {getter : state_type (string -> value)}
  (bool_cons : bool -> value)
  (num_cons : nat -> value)
  (e : expr) : state_type value :=
  match e with
  | EVal x => returnM (extract x)
  | EVar x => st << getter ;
      returnM (st x)
  | EPlus e1 e2 => 
      v1 << (shared_eval_expr bool_cons num_cons e1) ;
      v2 << (shared_eval_expr bool_cons num_cons e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (num_cons (Numerical.plus_op n1 n2))
  | EMult e1 e2 =>
      v1 << (shared_eval_expr bool_cons num_cons e1) ;
      v2 << (shared_eval_expr bool_cons num_cons e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (num_cons (Numerical.mult_op n1 n2))
  | EEq e1 e2 =>
      v1 << (shared_eval_expr bool_cons num_cons e1) ;
      v2 << (shared_eval_expr bool_cons num_cons e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (bool_cons (Numerical.eq_op n1 n2))
  | ELe e1 e2 =>
      v1 << (shared_eval_expr bool_cons num_cons e1) ;
      v2 << (shared_eval_expr bool_cons num_cons e2) ;
      n1 << (Numerical.ensure_numerical v1) ;
      n2 << (Numerical.ensure_numerical v2) ;
      returnM (bool_cons (Numerical.le_op n1 n2))
  | ENot e =>
      v << (shared_eval_expr bool_cons num_cons e) ;
      b << (BoolType.ensure_boolean v) ;
      returnM (bool_cons (BoolType.neg_op b))
  | EAnd e1 e2 =>
      v1 << (shared_eval_expr bool_cons num_cons e1) ;
      v2 << (shared_eval_expr bool_cons num_cons e2) ;
      b1 << (BoolType.ensure_boolean v1) ;
      b2 << (BoolType.ensure_boolean v2) ;
      returnM (bool_cons (BoolType.and_op b1 b2))
  end.

(*Fixpoint shared_aexp 
  {state_type : Type -> Type} 
  `{Monad state_type}
  (V : Type)
  (extraction : nat -> V)
  (plus_op mult_op : V -> V -> V)
  (store_type : Type)
  (getter : state_type (string -> V))
  (e : aexp) : state_type V :=
  match e with 
  | ANum n => returnM (extraction n)
  | AVar x =>
      st << getter ;
      returnM (st x)
  | APlus e1 e2 =>
      v1 << (shared_aexp V extraction plus_op mult_op store_type getter e1) ;
      v2 << (shared_aexp V extraction plus_op mult_op store_type getter e2) ;
      returnM (plus_op v1 v2)
  | AMult e1 e2 =>
      v1 << (shared_aexp V extraction plus_op mult_op store_type getter e1) ;
      v2 << (shared_aexp V extraction plus_op mult_op store_type getter e2) ;
      returnM (mult_op v1 v2)
  end.
*)
(*Fixpoint shared_bexp (S BV NV : Type) 
  (extract_b : bool -> BV)
  (extract_n : nat -> NV)
  (equals_op : NV -> NV -> BV)
  (le_op : NV -> NV -> BV)
  (neg_op : BV -> BV)
  (and_op : BV -> BV -> BV)
  (e : bexp) :
  State S BV :=
  match e with
  | BTrue => returnM (extraction true)
  | BFalse => returnM (extraction false)
  | BEq e1 e2 =>
      v1 << (shared_aexp S NV extract_n equals_op le_op neg_op and_op e1) ;
      v2 << (shared_aexp S NV extract_n equals_op le_op neg_op and_op e2) ;
      returnM (equals_op v1 v2)
  | BLe e1 e2 =>
      v1 << (shared_aexp S BN NV extraction equals_op le_op neg_op and_op e1) ;
      v2 << (shared_aexp S BN NV extraction equals_op le_op neg_op and_op e2) ;
      returnM (le_op v1 v2)
  | BNot b1 =>
      v1 << (shared_bexp S BN NV extraction equals_op le_op neg_op and_op b1) ;
      returnM (neg_op v1)
  | BAnd b1 b2 =>
      v1 << (shared_bexp S BN NV extraction equals_op le_op neg_op and_op b1) ;
      v2 << (shared_bexp S BN NV extraction equals_op le_op neg_op and_op b2) ;
      returnM (and_op v1 v2)
  end.*)
