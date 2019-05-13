Require Import Language.
Require Import Monad.

Fixpoint shared_aexp 
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
