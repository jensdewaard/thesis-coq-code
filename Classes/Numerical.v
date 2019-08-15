
Class Numerical {valType : Type} {M : Type -> Type} 
  {boolType : Type} (natType : Type) : Type :=
{
  ensure_numerical : valType -> M natType;
  plus_op : natType -> natType -> natType;
  mult_op : natType -> natType -> natType;
  eq_op   : natType -> natType -> boolType;
  le_op   : natType -> natType -> boolType;
}.

(* Sven's version, for reference:
Class Numerical {valType : Type} {M : Type -> Type} : Type :=
{
  plus_op : valType -> valType -> M valType;
  mult_op : valType -> valType -> M valType;
  eq_op   : valType -> valType -> M valType;
  le_op   : valType -> valType -> M valType;
}.
*)

Arguments Numerical {_ _ _} natType.
Arguments Build_Numerical {_ _ _} natType {_ _ _ _ _}.

