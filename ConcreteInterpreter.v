Require Import Coq.Arith.Arith.
Require Import Utf8.

Require Import Language.
Require Import Maps.
Require Import Monad.
Require Import AbstractStore.

Open Scope com_scope.

Fixpoint eval_aexp (e : aexp) : State store nat := 
  match e with
  | ANum n => returnM n
  | AVar x => 
      st << get ;
      returnM (st x)
  | APlus e1 e2 => 
      n1 << (eval_aexp e1) ;
      n2 << (eval_aexp e2) ;
      returnM (n1 + n2)
  | AMult e1 e2 => 
      n1 << (eval_aexp e1) ;
      n2 << (eval_aexp e2) ;
      returnM (n1 * n2)
  end.

Fixpoint eval_bexp (e : bexp) : State store bool :=
  match e with
  | BTrue => returnM true
  | BFalse => returnM false
  | BEq a1 a2 =>
      n1 << (eval_aexp a1) ;
      n2 << (eval_aexp a2) ;
      returnM (Nat.eqb n1 n2)
  | BLe a1 a2 =>
      n1 << (eval_aexp a1) ;
      n2 << (eval_aexp a2) ;
      returnM (Nat.leb n1 n2)
  | BNot b => 
      b' << (eval_bexp b) ;
      returnM (negb b')
  | BAnd b1 b2 =>
      b1' << (eval_bexp b1) ;
      b2' << (eval_bexp b2) ;
      returnM (andb b1' b2')
  end.

Definition eval_if {S A} (b : bool) (st1 st2 : State S A) : State S A :=
  if b then st1 else st2.

Definition eval_catch {S A} (st1 st2 : State S A) : State S A :=
  fun st => match (st1 st) with
  | None => (st2 st)
  | x => x
  end.

Fixpoint ceval (c : com) : State store unit :=
  match c with
  | CSkip => returnM tt
  | c1 ;c; c2 => 
      (ceval c1) ;; (ceval c2)
  | x ::= a => 
      n << (eval_aexp a) ;
      st << get ;
      put (t_update st x n)
  | CIf b c1 c2 => 
      b' << (eval_bexp b) ;
      eval_if b' (ceval c1) (ceval c2)
  | try c1 catch c2 => eval_catch (ceval c1) (ceval c2)
  | CFail => fail
  end.
