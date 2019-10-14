Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Nat.
Require Import Instances.Preorder.Pairs.
Require Import Types.Interval.

Global Instance preorder_interval : PreorderedSet interval.
Proof.
  unfold interval. apply preorder_pairs.
Qed.
