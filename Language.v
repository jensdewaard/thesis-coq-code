Require Export Coq.Strings.String.
Require Import Parity.
Require Import AbstractBool.

Inductive value : Type :=
  | VNat : nat -> value
  | VBool : bool -> value
  | VAbstractBool : abstr_bool -> value
  | VParity : parity -> value.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AVar : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CSeq : com -> com -> com
  | CAss : string -> aexp -> com
  | CIf  : bexp -> com -> com -> com
  | CTryCatch : com -> com -> com
  | CFail : com.

Bind Scope com_scope with com.
Notation "'SKIP'" :=
     CSkip : com_scope.
Notation "c1 ;c; c2" :=
    (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "x '::=' a" :=
    (CAss x a) (at level 60) : com_scope.
Notation "'try' c1 'catch' c2" :=
    (CTryCatch c1 c2) (at level 70) : com_scope.

Definition plus_op (v1 v2 : value) : option value :=
  match v1, v2 with
  |  VNat x, VNat y =>  Some (VNat (plus x y))
  |  VParity x, VParity y => Some (VParity (parity_plus x y))
  | _, _ => None
  end.
