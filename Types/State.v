Require Import Utf8.

Definition State (S A : Type) := S -> (A * S).
Definition StateT S M A : Type := S → M (A*S)%type.

