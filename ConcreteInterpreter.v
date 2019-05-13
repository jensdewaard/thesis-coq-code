Require Import Coq.Arith.Arith.
Require Import Utf8.

Require Import AbstractStore.
Require Import Statements.
Require Import Maps.
Require Import Monad.
Require Import State.
Require Import SharedInterpreter.
Require Import Result.

Open Scope com_scope.

Definition concrete_aexp := shared_aexp 
  nat 
  (fun x => x) 
  plus 
  mult 
  store
  get.

Fixpoint eval_bexp (e : bexp) : State bool :=
  match e with
  | BTrue => returnM true
  | BFalse => returnM false
  | BEq a1 a2 =>
      n1 << (concrete_aexp a1) ;
      n2 << (concrete_aexp a2) ;
      returnM (Nat.eqb n1 n2)
  | BLe a1 a2 =>
      n1 << (concrete_aexp a1) ;
      n2 << (concrete_aexp a2) ;
      returnM (Nat.leb n1 n2)
  | BNot b => 
      b' << (eval_bexp b) ;
      returnM (negb b')
  | BAnd b1 b2 =>
      b1' << (eval_bexp b1) ;
      b2' << (eval_bexp b2) ;
      returnM (andb b1' b2')
  end.

Definition eval_if {A} (b : bool) (st1 st2 : State A) : State A :=
  if b then st1 else st2.

Definition eval_catch {A} (st1 st2 : State A) : State A :=
  fun st => match (st1 st) with
  | (crashed _, st') => (crashed A, st')
  | (exception _, st') => (st2 st')
  | x => x
  end.

Fixpoint ceval (c : com) : State unit :=
  match c with
  | CSkip => returnM tt
  | c1 ;c; c2 => 
      (ceval c1) ;; (ceval c2)
  | x ::= a => 
      n << (concrete_aexp a) ;
      st << get ;
      put (t_update st x n)
  | CIf b c1 c2 => 
      b' << (eval_bexp b) ;
      eval_if b' (ceval c1) (ceval c2)
  | try c1 catch c2 => eval_catch (ceval c1) (ceval c2)
  | CFail => fail
  end.
