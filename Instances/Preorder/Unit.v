Require Import Classes.PreorderedSet.

Inductive unit_le : unit -> unit -> Prop :=
  | unit_le_refl : forall x, unit_le x x.

Lemma unit_le_trans : forall a b c,
  unit_le a b -> unit_le b c -> unit_le a c.
Proof.
  intros. destruct a, b, c. assumption.
Qed.

Instance preorder_unit : PreorderedSet unit :=
{
  preorder := unit_le;
  preorder_refl := unit_le_refl;
  preorder_trans := unit_le_trans;
}.

