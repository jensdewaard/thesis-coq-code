Class BoolType 
  {V : Type}
  {state : Type -> Type }
  (B : Type)
  : Type :=
{
  ensure_boolean : V -> state B;
  and_op : B -> B -> B;
  neg_op : B -> B;
}.
