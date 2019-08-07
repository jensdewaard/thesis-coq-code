Require Import Coq.Bool.Bool.

Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Types.AbstractBool.
Require Import Instances.Preorder.AbstractBoolean.

Definition gamma_bool (ab: abstr_bool) (b : bool) : Prop :=
  match ab with
  | ab_true   => Is_true b
  | ab_false  => ~Is_true b
  | ab_top    => True
  | ab_bottom => False
end.

Lemma gamma_bool_monotone : monotone gamma_bool.
Proof.
  unfold monotone. intros b1 b2 ?.
  destruct b1, b2; constructor; intros; destruct x; simpl in *; 
  try inversion H0; try inversion H; try tauto. 
Qed.

Instance galois_boolean : Galois bool abstr_bool :=
{
  gamma := gamma_bool;
  gamma_monotone := gamma_bool_monotone;
}.

