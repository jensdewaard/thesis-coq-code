Require Import Statements.
Require Import Monad.
(*Require Import Classes.Numerical.
Require Import Classes.BoolType.
Require Import Instances.Nat.Numerical.
Require Import Instances.BoolType.Boolean.
 *)
About nat_nat.

(** MOVE ME BACK LATER *)
Class IsBool (M : Type -> Type)
  (valType boolType : Type) : Type :=
{
  ensure_bool  : valType -> M boolType;
  build_bool   : boolType -> M valType;
  extract_bool : bool -> M boolType;
  and_op       : boolType -> boolType -> M boolType;
  neg_op       : boolType -> M boolType;
  if_op        : boolType -> M unit -> M unit -> M unit;
}.

Class IsNat (M : Type -> Type)
  (valType boolType natType : Type) : Type :=
{
  ensure_nat  : valType -> M natType;
  build_nat   : natType -> M valType;
  extract_nat : nat -> M natType;
  plus_op     : natType -> natType -> M natType;
  mult_op     : natType -> natType -> M natType;
  eq_op       : natType -> natType -> M boolType;
  le_op       : natType -> natType -> M boolType;
}.

Class Store (M : Type -> Type) (valType : Type) :=
{
  get : string -> M valType
}.

Class Except (M : Type -> Type) := {
  throw    : M unit;
  trycatch : M unit -> M unit -> M unit;
}.

Definition admit {A} : A. Admitted.

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
  | _ => admit
  end.

(*
  | ELe e1 e2 =>
      v1 << (shared_eval_expr e1) ;
      v2 << (shared_eval_expr e2) ;
      n1 << (ensure_nat v1) ;
      n2 << (ensure_nat v2) ;
      returnM (le_op n1 n2)
  | ENot e =>
      v << (shared_eval_expr e) ;
      b << (BoolType.ensure_boolean v) ;
      returnM (BoolType.neg_op b)
  | EAnd e1 e2 =>
      v1 << (shared_eval_expr e1) ;
      v2 << (shared_eval_expr e2) ;
      b1 << (BoolType.ensure_boolean v1) ;
      b2 << (BoolType.ensure_boolean v2) ;
      returnM (BoolType.and_op b1 b2)
  end.
*)

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
