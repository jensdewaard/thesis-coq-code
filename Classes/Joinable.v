Require Export Base.
Require Import Classes.PreorderedSet.

Class Joinable (T : Type) `{T_preorder : PreorderedSet T} : Type :=
{
  join_op : T -> T -> T;
  join_idem : ∀ x, join_op x x = x;
  join_upper_bound_left: forall t t', preorder t (join_op t t');
  join_assoc : ∀ x y z : T, 
    join_op x (join_op y z) = join_op (join_op x y) z;
  join_comm : ∀ x y, join_op x y = join_op y x;
}.

Corollary join_upper_bound_right {T : Type} `{Joinable T} : ∀ t t',
  preorder t' (join_op t t').
Proof.
  intros. rewrite join_comm. apply join_upper_bound_left.
Qed.

Arguments join_op : simpl never.
Hint Resolve join_upper_bound_left join_upper_bound_right : soundness.
Hint Rewrite @join_idem : soundness.

Infix "⊔" := join_op (at level 40).
