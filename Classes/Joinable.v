Require Export Base.
Require Import Classes.PreorderedSet.

Class Joinable (T : Type) `{T_preorder : PreorderedSet T} : Type :=
{
  join_op : T -> T -> T;
  join_upper_bound_left: forall t t', preorder t (join_op t t');
  join_upper_bound_right: forall t t', preorder t' (join_op t t');
  join_assoc : ∀ x y z : T, 
    join_op x (join_op y z) = join_op (join_op x y) z;
}.
Arguments join_op : simpl never.
Hint Resolve join_upper_bound_left join_upper_bound_right : soundness.

