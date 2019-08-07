Require Import Coq.Arith.Arith.
Require Import Utf8.

Require Import Types.AbstractStore.
Require Import Language.Statements.
Require Import Maps.
Require Import Monad.
Require Import State.
Require Import SharedInterpreter.
Require Import Types.Result.

Open Scope com_scope.

(*Definition concrete_aexp := shared_aexp 
  nat 
  (fun x => x) 
  plus 
  mult 
  store
  get.*)
  
Definition ensure_nat (v : cvalue) : State nat :=
  fun st => match v with
            | VNat x => returnR nat store x st
            | _ => crashed _ _
            end.
            
Definition ensure_bool (v : cvalue) : State bool :=
  fun st => match v with
            | VBool b => returnR bool store b st
            | _ => crashed _ _
            end.
  
Fixpoint eval_expr (e : expr) : State cvalue :=
  match e with
  | EVal x => returnM x
  | EVar x => st << get ;
      returnM (st x)
  | EPlus e1 e2 => 
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (ensure_nat v1) ;
      n2 << (ensure_nat v2) ;
      returnM (VNat (n1 + n2))
  | EMult e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (ensure_nat v1) ;
      n2 << (ensure_nat v2) ;
      returnM (VNat (n1 * n2))
  | EEq e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (ensure_nat v1) ;
      n2 << (ensure_nat v2) ;
      returnM (VBool (Nat.eqb n1 n2))
  | ELe e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      n1 << (ensure_nat v1) ;
      n2 << (ensure_nat v2) ;
      returnM (VBool (Nat.leb n1 n2))
  | ENot e =>
      v << (eval_expr e) ;
      b << (ensure_bool v) ;
      returnM (VBool (negb b))
  | EAnd e1 e2 =>
      v1 << (eval_expr e1) ;
      v2 << (eval_expr e2) ;
      b1 << (ensure_bool v1) ;
      b2 << (ensure_bool v2) ;
      returnM (VBool (andb b1 b2))
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
