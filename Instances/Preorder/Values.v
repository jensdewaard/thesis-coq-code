Require Import Coq.Classes.RelationClasses.

Require Import Classes.PreorderedSet.
Require Import Language.Statements.
Require Import Instances.Preorder.AbstractBoolean.
Require Import Instances.Preorder.Parity.
Require Import Instances.Preorder.Pairs.
Require Import Instances.Preorder.Interval.

Inductive avalue_le : avalue -> avalue -> Prop :=
  | avalue_le_par : forall x y, 
      preorder x y -> avalue_le (VParity x) (VParity y)
  | avalue_le_bool : forall b c,
      preorder b c -> avalue_le (VAbstrBool b) (VAbstrBool c)
  | avalue_le_interval : forall i j,
      preorder i j -> avalue_le (VInterval i) (VInterval j)
  | avalue_le_top : forall v,
      avalue_le v VTop
  | avalue_le_bot : forall v,
      avalue_le VBottom v.

Lemma avalue_le_trans : Transitive avalue_le.
Proof.
  unfold Transitive. intros x y z Hxy Hyz.
  inversion Hxy; subst;
  inversion Hyz; subst; try constructor. 
  - eapply preorder_trans. apply H. apply H1.
  - eapply preorder_trans. apply H. apply H1.
  - eapply preorder_trans. apply H. apply H1.
Qed.

Lemma avalue_le_refl : Reflexive avalue_le.
Proof. 
  unfold Reflexive. intro x. destruct x; constructor; apply preorder_refl.
Qed.

Global Instance avalue_preorder : PreorderedSet avalue :=
{
  preorder := avalue_le;
  preorder_refl := avalue_le_refl;
  preorder_trans := avalue_le_trans;
}.

