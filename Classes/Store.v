Require Export Coq.Strings.String.

Class Store (M : Type -> Type) (valType : Type) :=
{
  get : string -> M valType;
  put : string -> valType -> M unit;
}.
