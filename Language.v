Require Export Coq.Strings.String.

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
  | CAss : string -> aexp -> com.

Bind Scope com_scope with com.
Notation "'SKIP'" :=
     CSkip : com_scope.
Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "x '::=' a" :=
    (CAss x a) (at level 60) : com_scope.
