Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Values.
Require Import Language.Statements.
Require Import Instances.Galois.Parity.
Require Import Instances.Galois.AbstractBoolean.

Section galois_values.

Definition gamma_value : avalue -> cvalue -> Prop :=
  fun av => fun cv => match av, cv with
                      | VParity p, VNat n => gamma p n
                      | VAbstrBool ab, VBool b => gamma ab b
                      | VTop, _ => True
                      | _, _ => False
                      end.

Lemma gamma_value_monotone : monotone gamma_value.
Proof.
  unfold monotone. intros a a' Hpre.
  inversion Hpre; subst.
  - simpl in *. constructor. intros z Hgamma.
    destruct z. simpl in Hgamma. simpl. 
    inversion H; subst.
    + reflexivity.
    + inversion Hgamma.
    + apply Hgamma.
    + inversion Hgamma.
  - simpl in *. constructor. intros d Hgamma.
    destruct d. inversion Hgamma.
    simpl in *. inversion H; subst.
    + inversion Hgamma.
    + reflexivity.
    + apply Hgamma.
  - constructor. intros. constructor.
  - constructor. intros. inversion H.
Qed.

Global Instance galois_values : Galois cvalue avalue := 
{
  gamma := gamma_value;
  gamma_monotone := gamma_value_monotone;
}.
End galois_values.

