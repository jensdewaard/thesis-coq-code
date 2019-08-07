Require Import Classes.PreorderedSet.

Class Joinable (T : Type) `{PreorderedSet T} : Type :=
{
  join_op : T -> T -> T;
  join_upper_bound_left: forall t t', preorder t (join_op t t');
  join_upper_bound_right: forall t t', preorder t' (join_op t t');
}.

