Require Import AbstractStore.
Require Import AbstractBool.
Require Import ConcreteInterpreter.
Require Import Language.
Require Import Maps.
Require Import Monad.
Require Import Parity.

Open Scope com_scope.

Fixpoint abstract_eval_aexp (e : aexp) : State parity :=
  match e with 
  | ANum n => returnM (extract_par n)
  | AVar x =>
      st << get ;
      returnM (st x)
  | APlus p1 p2 => 
      p1' << (abstract_eval_aexp p1) ;
      p2' << (abstract_eval_aexp p2) ;
      returnM (parity_plus p1' p2')
  | AMult p1 p2 =>
      p1' << (abstract_eval_aexp p1) ;
      p2' << (abstract_eval_aexp p2) ;
      returnM (parity_mult p1' p2')
  end.

Fixpoint beval_abstract (b : bexp) : State abstr_bool :=
  match b with
  | BFalse => returnM (ab_false)
  | BTrue => returnM (ab_true)
  | BEq e1 e2 => 
      e1' << (abstract_eval_aexp e1) ;
      e2' << (abstract_eval_aexp e2) ;
      returnM (parity_eq e1' e2')
  | BLe e1 e2=> return_state ab_top
  | BNot b => 
      b' << (beval_abstract b) ;
      returnM (neg_ab b')
  | BAnd b1 b2 =>
      b1' << (beval_abstract b1) ;
      b2' << (beval_abstract b2) ;
      returnM (and_ab b1' b2')
  end.

Definition eval_if_abstract {S A} (b : abstr_bool) (st1 st2 : @State S A) 
  : @State S A :=
  match b with
  | ab_true   => st1
  | ab_false  => st2
  | ab_top    => fail
  | ab_bottom => fail
  end.

Fixpoint ceval_abstract (c : com) : State unit :=
  match c with
  | CSkip => return_state tt
  | c1 ;c; c2 =>
      (ceval_abstract c1) ;; (ceval_abstract c2)
  | x ::= a => 
      p << (abstract_eval_aexp a) ;
      st << get ;
      put (t_update st x p)
  | CIf b c1 c2 => 
      b' << (beval_abstract b) ;
      eval_if_abstract b' (ceval_abstract c1) (ceval_abstract c2)
  | try c1 catch c2 => eval_catch (ceval_abstract c1) (ceval_abstract c2)
  | CFail => fail
  end.

(* write a project plan not a thesis 
  
technical plan:
  extract shared interpreter
  define lemmas
  rewrite operations on datatypes as monads

writing plan:
  project plan <----
  document what is done
  mention precision vs. soundness
  sense of direction
  presentation

case study:
  taint analysis
  *)
