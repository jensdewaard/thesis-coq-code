Class IsNat (M : Type -> Type)
  (valType boolType natType : Type) : Type :=
{
  ensure_nat  : valType -> M natType;
  build_nat   : natType -> M valType;
  extract_nat : nat -> M natType;
  plus_op     : natType -> natType -> M natType;
  mult_op     : natType -> natType -> M natType;
  eq_op       : natType -> natType -> M boolType;
  le_op       : natType -> natType -> M boolType;
}.
