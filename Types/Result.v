(* results *)

Require Import Coq.Classes.RelationClasses.

Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.

Inductive result (A S : Type) : Type :=
  | returnR : A -> S -> result A S
  | crashed : result A S
  | exception : S -> result A S.

Arguments returnR {_ _}.
Arguments crashed {_ _}.
Arguments exception {_ _}.
  
Inductive abstract_result (A S : Type) :=
  | returnRA : A -> S -> abstract_result A S
  | crashedA : abstract_result A S
  | exceptionA : S -> abstract_result A S
  | exceptionOrReturn : A -> S -> abstract_result A S.

Arguments returnRA {_ _}.
Arguments crashedA {_ _}.
Arguments exceptionA {_ _}.
Arguments exceptionOrReturn {_ _}.


