Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Functions.
Require Import Instances.Preorder.Values.
Require Import Types.Stores.

Instance preordered_abstract_store : PreorderedSet abstract_store
:= {
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.
