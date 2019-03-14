Require Import Coq.Arith.Arith.
Require Import Utf8.

Require Import Language.
Require Import Maps.
Require Import Monad.
Require Import AbstractStore.

Definition state := total_map nat.

Open Scope com_scope.

Fixpoint eval_aexp (e : aexp) : State nat := 
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
      returnM (n1 + n2)
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

Definition eval_if {S A} (b : bool) (st1 st2 : @State S A) : @State S A :=
  if b then st1 else st2.

Print fail.
Print State.


Definition eval_catch {S A} (st1 st2 : @State S A) : @State S A :=
  fun st => match (st1 st) with
  | None => (st2 st)
  | _ => (st1 st)
  end.

Fixpoint ceval (c : com) : State unit :=
  match c with
  | CSkip => return_state tt
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
  end.
