Require Export Coq.Strings.String.
Require Import Classes.Monad.

Class Store (S : Type) (M : Type -> Type) `{inst : Monad M} :=
{
  get : M S;
  put : S -> M unit;
}.
