Require Export Base Coq.Strings.String.
Require Import Classes.Monad.

Class MonadState (S : Type) (M : Type -> Type) `{M_monad : Monad M} :=
{
  get : M S;
  put : S -> M unit;
}.
