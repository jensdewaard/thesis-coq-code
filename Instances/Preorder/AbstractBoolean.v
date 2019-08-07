Require Import Classes.PreorderedSet.
Require Import Types.AbstractBool.

Inductive ab_le : abstr_bool -> abstr_bool -> Prop :=
  | ab_le_bottom : forall ab, ab_le ab_bottom ab
  | ab_le_top : forall ab, ab_le ab ab_top
  | ab_le_refl : forall ab, ab_le ab ab.

Lemma ab_le_trans :forall a b c,
  ab_le a b -> ab_le b c -> ab_le a c.
Proof. 
  intros. destruct a, b, c; try constructor; try inversion H0; 
  try inversion H.
Qed.

Instance preorder_ab : PreorderedSet abstr_bool :=
{
  preorder := ab_le;
  preorder_refl := ab_le_refl;
  preorder_trans := ab_le_trans;
}.

