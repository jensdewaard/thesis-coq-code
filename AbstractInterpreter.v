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

Definition abstract_aexp := shared_aexp 
  parity 
  extract_par 
  parity_plus 
  parity_mult
  abstract_store
  get_abstract.

Fixpoint beval_abstract (b : bexp) : AbstractState abstr_bool :=
  match b with
  | BFalse => returnM (ab_false)
  | BTrue => returnM (ab_true)
  | BEq e1 e2 => 
      e1' << (abstract_aexp e1) ;
      e2' << (abstract_aexp e2) ;
      returnM (parity_eq e1' e2')
  | BLe e1 e2=> 
     e1' << (abstract_aexp e1) ;
     e2' << (abstract_aexp e2) ;
     returnM (ab_top)
  | BNot b => 
      b' << (beval_abstract b) ;
      returnM (neg_ab b')
  | BAnd b1 b2 =>
      b1' << (beval_abstract b1) ;
      b2' << (beval_abstract b2) ;
      returnM (and_ab b1' b2')
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
  | (crashed _, st') => (crashed A, st')
  | (exception _, st') => st2 st'
  | x => x
  end.

Fixpoint ceval_abstract (c : com) : AbstractState unit :=
  match c with
  | CSkip => returnM tt
  | c1 ;c; c2 =>
      (ceval_abstract c1) ;; (ceval_abstract c2)
  | x ::= a => 
      p << (abstract_aexp a) ;
      st << get_abstract ;
      put_abstract (t_update st x p)
  | CIf b c1 c2 => 
      b' << (beval_abstract b) ;
      eval_if_abstract b' (ceval_abstract c1) (ceval_abstract c2)
  | try c1 catch c2 => 
      eval_catch_abstract (ceval_abstract c1) (ceval_abstract c2)
  | CFail => fail_abstract
  end.
