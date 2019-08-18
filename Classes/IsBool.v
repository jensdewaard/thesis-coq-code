Class IsBool (M : Type -> Type)
  (valType boolType : Type) : Type :=
{
  ensure_bool  : valType -> M boolType;
  build_bool   : boolType -> M valType;
  extract_bool : bool -> M boolType;
  and_op       : boolType -> boolType -> M boolType;
  neg_op       : boolType -> M boolType;
  if_op        : boolType -> M unit -> M unit -> M unit;
}.
