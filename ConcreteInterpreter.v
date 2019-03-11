Require Import Coq.Arith.Arith.

Require Import Language.
Require Import Maps.
Require Import Monad.

Definition state := total_map nat.

Open Scope com_scope.

Fixpoint eval_aexp (e : aexp) : State nat := 
  match e with
  | ANum n => return_state n
  | AVar x => bind_state get (fun st => return_state (st x))
  | APlus e1 e2 => 
      bind_state (eval_aexp e1) 
        (fun n1 => bind_state (eval_aexp e2) 
          (fun n2 => return_state (n1 + n2)))
  | AMult e1 e2 => 
      bind_state (eval_aexp e2)
        (fun n1 => bind_state (eval_aexp e2)
          (fun n2 => return_state (n1 * n2)))
  end.

Fixpoint eval_bexp (e : bexp) : State bool :=
  match e with
  | BTrue => return_state true
  | BFalse => return_state false
  | BEq a1 a2 =>
      bind_state (eval_aexp a1)
        (fun n1 => bind_state (eval_aexp a2)
          (fun n2 => return_state (Nat.eqb n1 n2)))
  | BLe a1 a2 =>
      bind_state (eval_aexp a2)
        (fun n1 => bind_state (eval_aexp a2)
          (fun n2 => return_state (Nat.leb n1 n2)))
  | BNot b => 
      bind_state (eval_bexp b) (fun b => return_state (negb b))
  | BAnd b1 b2 =>
      bind_state (eval_bexp b1) 
        (fun b1 => bind_state (eval_bexp b2)
          (fun b2 => return_state (andb b1 b2)))
  end.

Definition eval_if (b : bool) (st1 st2 : state) : state :=
  if b then st1 else st2.

Fixpoint ceval (c : com) : State unit :=
  match c with
  | CSkip => return_state tt
  | c1 ;; c2 => 
      bind_state (ceval c1) (fun _ => ceval c2)
  | x ::= a => bind_state (eval_aexp a) (fun (n : nat) => 
      bind_state get (fun st => put (t_update st x n)))
  end.
