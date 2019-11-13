Require Export Coq.Strings.String.
Require Import Classes.Monad.

Class Store (S : Type) (M : Type -> Type) `{inst : Monad M} (V : Type) :=
{
  get : M S;
  put : S -> M unit;
  retrieve : string -> M V;
  update : string -> V -> M S;
}.
