Require Import AbstractState.
Require Import AbstractBool.
Require Import ConcreteInterpreter.
Require Import Language.
Require Import Maps.
Require Import Parity.

Open Scope com_scope.

Fixpoint abstract_eval_aexp (st : abstract_state) (e : aexp) : parity :=
  match e with 
  | ANum n => extract_par n
  | AVar x => (st x)
  | APlus p1 p2 => 
      parity_plus (abstract_eval_aexp st p1) (abstract_eval_aexp st p2)
  | AMult p1 p2 =>
      parity_mult (abstract_eval_aexp st p1) (abstract_eval_aexp st p2)
  end.

Definition sound_aexp (e : aexp) := forall ast st,
  sound_state ast st -> 
  sound_par (abstract_eval_aexp ast e) (eval_aexp st e).

Fixpoint beval_abstract (st : abstract_state) (b : bexp) : abstr_bool :=
  match b with
  | BFalse => ab_false
  | BTrue => ab_true
  | BEq e1 e2 => match (abstract_eval_aexp st e1), (abstract_eval_aexp st e2) with
                 | par_even, par_odd => ab_false
                 | par_odd, par_even => ab_false
                 | _, _ => ab_top
                 end
  | BLe e1 e2=> ab_top
  | BNot b => neg_ab (beval_abstract st b)
  | BAnd b1 b2 => and_ab (beval_abstract st b1) (beval_abstract st b2)
  end.

Definition sound_bexp (b : bexp) := forall ast st,
  sound_state ast st ->
  sound_ab (beval_abstract ast b) (eval_bexp st b).

Fixpoint ceval_abstract (st : abstract_state) (c : com) : abstract_state :=
  match c with
  | CSkip => st
  | c1 ;; c2 =>
      let st' := ceval_abstract st c1 in
      ceval_abstract st' c2
  | x ::= a => t_update st x (abstract_eval_aexp st a)
  end.

Definition sound_com (c : com) := forall ast st,
  sound_state ast st -> 
  sound_state (ceval_abstract ast c) (ceval st c).

