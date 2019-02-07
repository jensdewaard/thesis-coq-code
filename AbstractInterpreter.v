Require Import AbstractState.
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

