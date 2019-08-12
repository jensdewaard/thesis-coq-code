Class Numerical {T  : Type} 
  {state : (Type -> Type)} 
  {boolType : Type}
  (N : Type) 
  : Type :=
{
  ensure_numerical : T -> state N;
  plus_op : N -> N -> N;
  mult_op : N -> N -> N;
  eq_op   : N -> N -> boolType;
  le_op   : N -> N -> boolType;
}.

Arguments Numerical {_ _ _} N.
Arguments Build_Numerical {_ _ _} N {_ _ _ _ _}.

