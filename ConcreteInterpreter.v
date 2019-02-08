Require Import Coq.Arith.Arith.

Require Import Language.
Require Import Maps.

Definition state := total_map nat.

Open Scope com_scope.

Fixpoint eval_aexp (st : state) (e : aexp) : nat := 
  match e with
  | ANum n => n
  | AVar x => st x
  | APlus e1 e2 => eval_aexp st e1 + eval_aexp st e2
  | AMult e1 e2 => eval_aexp st e1 * eval_aexp st e2
  end.

Fixpoint eval_bexp (st : state) (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (eval_aexp st a1) (eval_aexp st a2)
  | BLe a1 a2 => Nat.leb (eval_aexp st a1) (eval_aexp st a2)
  | BNot b => negb (eval_bexp st b)
  | BAnd b1 b2 => andb (eval_bexp st b1) (eval_bexp st b2)
  end.

Fixpoint ceval (st : state) (c : com) : state :=
  match c with
  | CSkip => st
  | c1 ;; c2 => 
      let st' := ceval st c1 in
      ceval st' c2
  | x ::= a => t_update st x (eval_aexp st a)
  end.


