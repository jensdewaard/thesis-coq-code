Require Export Coq.Strings.String.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Parity.

Declare Scope com_scope.

Inductive cvalue : Type :=
  | VNat : nat -> cvalue
  | VBool : bool -> cvalue.

Inductive avalue : Type :=
  | VParity : parity -> avalue
  | VAbstrBool : abstr_bool -> avalue
  | VInterval : interval -> avalue
  | VTop : avalue
  | VBottom : avalue.

(* expand on the above *)

Inductive expr : Type :=
  | EVal : cvalue -> expr
  | EVar : string -> expr
  | EPlus : expr -> expr -> expr
  | EMult : expr -> expr -> expr
  | EEq : expr -> expr -> expr
  | ELe : expr -> expr -> expr
  | ENot : expr -> expr
  | EAnd : expr -> expr -> expr.

Inductive com : Type :=
  | CSkip : com
  | CSeq : com -> com -> com
  | CAss : string -> expr -> com
  | CIf  : expr -> com -> com -> com
  | CTryCatch : com -> com -> com
  | CThrow : com.

Bind Scope com_scope with com.
Notation "'SKIP'" :=
     CSkip : com_scope.
Notation "c1 ;c; c2" :=
    (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "x '::=' a" :=
    (CAss x a) (at level 60) : com_scope.
Notation "'try' c1 'catch' c2" :=
    (CTryCatch c1 c2) (at level 70) : com_scope.
Notation "'IF2' b 'THEN' c1 'ELSE' c2" :=
    (CIf b c1 c2) (at level 70) : com_scope.


(* zoek naar papers over 'auto' in coq, en het maken van proofs
  mogelijk falen *)

