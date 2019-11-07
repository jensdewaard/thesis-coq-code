Require Export Utf8.
Require Import Program.Basics.

Create HintDb soundness.

Ltac inv H := inversion H; subst; clear H.

Notation "f '$' x" := (f x)
  (at level 20, right associativity, only parsing).

Definition id := fun {A : Type} (a : A) => a.
Notation "f ∘ g" := (compose g f).
