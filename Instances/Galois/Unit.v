Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Unit.

Section galois_unit.
Definition gamma_unit : 
  unit -> unit -> Prop :=  
  fun tt tt => True.

Lemma gamma_unit_monotone : monotone gamma_unit.
Proof.
  unfold monotone.
  intros. simpl. constructor. reflexivity.
Qed.

Global Instance galois_unit : Galois unit unit := 
{
  gamma := gamma_unit;
  gamma_monotone := gamma_unit_monotone;
}. 
End galois_unit.

