Require Import Coq.Classes.RelationClasses.

Require Import Classes.PreorderedSet.

Section preordered_pairs.
Context {A B : Type} `{PreorderedSet A, PreorderedSet B}.

Inductive preorder_pair_le : 
  (prod A B) -> (prod A B) -> Prop :=
  | preorder_pair : forall (a a' : A) (b b' : B), 
      preorder a a' -> preorder b b' -> preorder_pair_le (a,b) (a',b').

Lemma preorder_pair_le_refl :
  Reflexive preorder_pair_le.
Proof. 
  intros a.
  destruct a. constructor; apply preorder_refl.
Qed.

Lemma preorder_pair_le_trans :
  Transitive preorder_pair_le.
Proof. 
  intros x y z. 
  intros. inversion H1; subst.  inversion H2; subst. constructor.
  - eapply preorder_trans. apply H3. apply H7.
  - eapply preorder_trans. apply H4. apply H9.
Qed.

Global Instance preorder_pairs : 
  PreorderedSet (A * B)%type :=
{
  preorder := preorder_pair_le;
  preorder_refl := preorder_pair_le_refl;
  preorder_trans := preorder_pair_le_trans;
}.
End preordered_pairs.

