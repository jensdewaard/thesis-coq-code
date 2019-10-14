Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Le.

Global Instance preorder_nat : PreorderedSet nat := 
{
  preorder := le;
  preorder_refl := le_refl;
  preorder_trans := le_trans;
}.

