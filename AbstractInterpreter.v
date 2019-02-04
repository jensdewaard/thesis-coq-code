Require Import Language.
Require Import Maps.
Require Import Parity.

Definition abstract_state := total_map (parity).

Open Scope com_scope.

Fixpoint abstract_eval_aexp (st : abstract_state) (e : aexp) : parity :=
  match e with 
  | ANum n => extract n
  | AVar x => (st x)
  | APlus p1 p2 => 
      parity_plus (abstract_eval_aexp st p1) (abstract_eval_aexp st p2)
  | AMult p1 p2 =>
      parity_mult (abstract_eval_aexp st p1) (abstract_eval_aexp st p2)
  end.

Fixpoint ceval_abstract (st : abstract_state) (c : com) : abstract_state :=
  match c with
  | CSkip => st
  | c1 ;; c2 =>
      let st' := ceval_abstract st c1 in
      ceval_abstract st' c2
  end.


