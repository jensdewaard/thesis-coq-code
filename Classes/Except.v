Require Export Base.
Require Import Classes.Applicative.
Require Import Classes.Monad.

Class Except (M : Type -> Type) `{Monad M} := {
  throw    : M unit;
  trycatch : M unit -> M unit -> M unit;
  bind_fail : forall (f : unit -> M unit), bindM throw f = throw;
  trycatch_throw_left : forall (x : M unit), 
    trycatch throw x = x;
  trycatch_throw_right : forall (x : M unit),
    trycatch x throw = x;
  trycatch_pure : forall x h, trycatch (pure x) h = pure x;
}.

Hint Rewrite @trycatch_throw_left @trycatch_throw_right 
  @trycatch_pure : soundness.
