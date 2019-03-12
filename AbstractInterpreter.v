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

Definition eval_if_abstract (b : abstr_bool) (st1 st2 : abstract_store) 
  : abstract_store :=
  match b with
  | ab_true   => st1
  | ab_false  => st2
  | ab_top    => abstract_store_join st1 st2
  | ab_bottom => abstract_store_bottom
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
  | CIf b c1 c2 => fail
  end.


