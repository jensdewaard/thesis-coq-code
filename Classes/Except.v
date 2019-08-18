Class Except (M : Type -> Type) := {
  throw    : M unit;
  trycatch : M unit -> M unit -> M unit;
}.
