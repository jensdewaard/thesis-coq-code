Require Classes.PreorderedSet.
Require Language.Parity.

Instance proset_parity : PreorderedSet parity :=
{
  preorder := parity_le;
  preorder_refl := parity_le_refl;
  preorder_trans := parity_le_trans;
}.
