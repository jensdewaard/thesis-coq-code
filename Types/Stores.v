Require Import Types.Maps.
Require Import Language.Statements.

Definition abstract_store := total_map avalue.
Definition store := total_map cvalue.

Definition abstract_update (s : abstract_store) (x : string) (v : avalue) :
  abstract_store := t_update s x v.

Definition concrete_update (s : store) (x : string) (v : cvalue) :
  store := t_update s x v.

