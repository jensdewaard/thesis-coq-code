Require Import Coq.Arith.Arith.
Require Import Utf8.

Require Import Language.
Require Import Maps.
Require Import Monad.

Definition state := total_map nat.

Open Scope com_scope.

Fixpoint eval_aexp (e : aexp) : State nat := 
  match e with
  | ANum n => return_state n
  | AVar x => 
      st << get ;
      return_state (st x)
  | APlus e1 e2 => 
      n1 << (eval_aexp e1) ;
      n2 << (eval_aexp e2) ;
      return_state (n1 + n2)
  | AMult e1 e2 => 
      n1 << (eval_aexp e1) ;
      n2 << (eval_aexp e2) ;
      return_state (n1 + n2)
  end.

Fixpoint eval_bexp (e : bexp) : State bool :=
  match e with
  | BTrue => return_state true
  | BFalse => return_state false
  | BEq a1 a2 =>
      n1 << (eval_aexp a1) ;
      n2 << (eval_aexp a2) ;
      return_state (Nat.eqb n1 n2)
  | BLe a1 a2 =>
      n1 << (eval_aexp a1) ;
      n2 << (eval_aexp a2) ;
      return_state (Nat.leb n1 n2)
  | BNot b => 
      b' << (eval_bexp b) ;
      return_state (negb b')
  | BAnd b1 b2 =>
      b1' << (eval_bexp b1) ;
      b2' << (eval_bexp b2) ;
      return_state (andb b1' b2')
  end.

Definition eval_if (b : bool) (st1 st2 : state) : state :=
  if b then st1 else st2.

Fixpoint ceval (c : com) : State unit :=
  match c with
  | CSkip => return_state tt
  | c1 ;c; c2 => 
      (ceval c1) ;; (ceval c2)
  | x ::= a => 
      n << (eval_aexp a) ;
      st << get ;
      put (t_update st x n)
  end.
