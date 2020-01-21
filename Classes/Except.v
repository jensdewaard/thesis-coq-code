Require Export Base.
Require Import Classes.Applicative.
Require Import Classes.Monad.

Implicit Type M : Type → Type.
Implicit Type A : Type.

Class Except M `{Monad M} := {
  throw    : forall {A}, M A;
  trycatch : forall {A}, M A -> M A -> M A;
  trycatch_throw_left : forall {A} (x : M A), 
    trycatch throw x = x;
  trycatch_throw_right : forall {A} (x : M A),
    trycatch x throw = x;
}.
Arguments throw : simpl never.

Hint Rewrite @trycatch_throw_left @trycatch_throw_right : soundness.
