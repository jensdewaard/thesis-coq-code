Require Export Base.
Require Import Types.Maps.
Require Import Language.Statements.

Definition abstract_store := total_map avalue.
Definition store := total_map cvalue.

Instance abstract_store_inhabited : Inhabited abstract_store := λ _, VTop.
Instance concrete_store_inhabited : Inhabited store := λ _, VNat 0.

Definition abstract_update (s : abstract_store) (x : string) (v : avalue) :
  abstract_store := t_update s x v.

Definition concrete_update (s : store) (x : string) (v : cvalue) :
  store := t_update s x v.


