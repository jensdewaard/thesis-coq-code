Require Import AbstractStore.
Require Import AbstractBool.
Require Import ConcreteInterpreter.
Require Import Statements.
Require Import Joinable.
Require Import Maps.
Require Import Monad.
Require Import Parity.
Require Import Result.
Require Import SharedInterpreter.
Require Import State.

Open Scope com_scope.

(*Definition abstract_aexp := shared_aexp 
  parity 
  extract_par 
  parity_plus 
  parity_mult
  abstract_store
  get_abstract.*)
  
Definition ensure_par (v : avalue) : AbstractState parity :=
  fun st => match v with
            | VParity x => returnRA parity abstract_store x st
            | _ => crashedA _ _
            end.
            
Definition ensure_abool (v : avalue) : AbstractState abstr_bool :=
  fun st => match v with
            | VAbstrBool b => returnRA abstr_bool abstract_store b st
            | _ => crashedA _ _
            end.
            
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
      n1 << (ensure_par v1) ;
      n2 << (ensure_par v2) ;
      returnM (VParity (parity_plus n1 n2))
  | EMult e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      n1 << (ensure_par v1) ;
      n2 << (ensure_par v2) ;
      returnM (VParity (parity_mult n1 n2))
  | EEq e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      n1 << (ensure_par v1) ;
      n2 << (ensure_par v2) ;
      returnM (VAbstrBool (parity_eq n1 n2))
  | ELe e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      n1 << (ensure_par v1) ;
      n2 << (ensure_par v2) ;
      returnM (VAbstrBool (ab_top))
  | ENot e =>
      v << (eval_expr_abstract e) ;
      b << (ensure_abool v) ;
      returnM (VAbstrBool (neg_ab b))
  | EAnd e1 e2 =>
      v1 << (eval_expr_abstract e1) ;
      v2 << (eval_expr_abstract e2) ;
      b1 << (ensure_abool v1) ;
      b2 << (ensure_abool v2) ;
      returnM (VAbstrBool (and_ab b1 b2))
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
  | x => x
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
      b' << (ensure_abool v) ;
      eval_if_abstract b' (ceval_abstract c1) (ceval_abstract c2)
  | try c1 catch c2 => 
      eval_catch_abstract (ceval_abstract c1) (ceval_abstract c2)
  | CFail => fail_abstract
  end.
