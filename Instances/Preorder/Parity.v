Require Import Classes.PreorderedSet.
Require Import Types.Parity.

Inductive parity_le : parity -> parity -> Prop :=
  | lt_top : forall p, parity_le p par_top
  | lt_bottom : forall p, parity_le par_bottom p
  | lt_refl : forall p, parity_le p p.

Lemma parity_le_refl : forall p, parity_le p p.
destruct p; constructor. Qed.

Lemma parity_le_trans : forall p1 p2 p3,
  parity_le p1 p2 -> parity_le p2 p3 -> parity_le p1 p3.
destruct p1, p2, p3; intros; try constructor; 
  try inversion H; try inversion H0. Qed.

Global Instance proset_parity : PreorderedSet parity :=
{
  preorder := parity_le;
  preorder_refl := parity_le_refl;
  preorder_trans := parity_le_trans;
}.
