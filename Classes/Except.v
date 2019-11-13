Require Export Base.
Require Import Classes.Applicative.
Require Import Classes.Monad.

Class Except (M : Type -> Type) `{Monad M} := {
  throw    : forall {A}, M A;
  trycatch : forall {A}, M A -> M A -> M A;
  bind_fail : forall {A} (f : unit -> M A), bindM throw f = throw;
  trycatch_throw_left : forall {A} (x : M A), 
    trycatch throw x = x;
  trycatch_throw_right : forall {A} (x : M A),
    trycatch x throw = x;
  trycatch_pure : forall {A} x h, trycatch (pure x) h = pure (A:=A) x;
}.

Hint Rewrite @trycatch_throw_left @trycatch_throw_right 
  @trycatch_pure : soundness.
