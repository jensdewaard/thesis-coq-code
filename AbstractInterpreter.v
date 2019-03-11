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
  | ANum n => return_state (extract_par n)
  | AVar x => 
      bind_state get (fun st => return_state (st x))
  | APlus p1 p2 => 
      bind_state (abstract_eval_aexp p1)
        (fun n1 => bind_state (abstract_eval_aexp p2)
          (fun n2 => return_state (parity_plus n1 n2)))
  | AMult p1 p2 =>
      bind_state (abstract_eval_aexp p1)
        (fun n1 => bind_state (abstract_eval_aexp p2)
          (fun n2 => return_state (parity_mult n1 n2)))
  end.

Fixpoint beval_abstract (b : bexp) : State abstr_bool :=
  match b with
  | BFalse => return_state (ab_false)
  | BTrue => return_state (ab_true)
  | BEq e1 e2 => 
      bind_state (abstract_eval_aexp e1)
        (fun n1 => bind_state (abstract_eval_aexp e2)
          (fun n2 => return_state (parity_eq n1 n2)))
  | BLe e1 e2=> return_state ab_top
  | BNot b => 
      bind_state (beval_abstract b)
        (fun b => return_state (neg_ab b))
  | BAnd b1 b2 => 
      bind_state (beval_abstract b1)
        (fun b1' => bind_state (beval_abstract b2)
          (fun b2' => return_state (and_ab b1' b2')))
  end.

Definition eval_if_abstract (b : abstr_bool) (st1 st2 : abstract_store) : abstract_store :=
  match b with
  | ab_true   => st1
  | ab_false  => st2
  | ab_top    => abstract_store_join st1 st2
  | ab_bottom => abstract_store_bottom
  end.

Fixpoint ceval_abstract (c : com) : State unit :=
  match c with
  | CSkip => return_state tt
  | c1 ;; c2 =>
      bind_state (ceval_abstract c1)
        (fun _ => ceval_abstract c2)
  | x ::= a => 
      bind_state (abstract_eval_aexp a)
        (fun n => bind_state get 
          (fun st => put (t_update st x n)))
  end.


