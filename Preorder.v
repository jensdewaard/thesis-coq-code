Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses.
Require Import AbstractBool.
Require Import AbstractStore.
Require Import Parity.
Require Import Language.Statements.
Require Import Classes.PreorderedSet.
  
Instance proset_parity : PreorderedSet parity :=
{
  preorder := parity_le;
  preorder_refl := parity_le_refl;
  preorder_trans := parity_le_trans;
}.

Instance preorder_ab : PreorderedSet abstr_bool :=
{
  preorder := ab_le;
  preorder_refl := ab_le_refl;
  preorder_trans := ab_le_trans;
}.


Lemma gamma_bool_monotone : monotone gamma_bool.
Proof.
  unfold monotone. intros b1 b2 ?.
  destruct b1, b2; constructor; intros; destruct x; simpl in *; 
    try inversion H0; try inversion H; try tauto. 
Qed.

Lemma gamma_par_monotone : forall p1 p2,
  preorder p1 p2 -> preorder (gamma_par p1) (gamma_par p2).
Proof.
  destruct p1, p2; simpl; intros; try constructor; try inversion H;
    intros; try tauto.
Qed.


Section preordered_functions.
Context {A A' : Type} `{PreorderedSet A'}.

Inductive pointwise_ordering : 
  (A->A') -> (A->A') -> Prop :=
  | pointwise : forall (f1 f2 : (A->A')),
      (forall x, preorder (f1 x) (f2 x)) -> pointwise_ordering f1 f2.

Lemma pointwise_ordering_refl : 
  Reflexive pointwise_ordering.
Proof. 
  intros f. constructor. intro x. apply preorder_refl.
Qed.

Lemma pointwise_ordering_trans : 
  Transitive pointwise_ordering.
Proof.
  constructor.
  intros. 
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  eapply preorder_trans. apply H2. apply H0.
Qed.

Global Instance preordered_function_spaces : 
  PreorderedSet (A->A') :=
{
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.
  
End preordered_functions.

Lemma preorder_props : forall {X : Type} (P Q : X -> Prop) (x : X),
  preorder P Q -> P x -> Q x.
Proof. 
  intros. simpl in H. destruct H. apply H. apply H0.
Qed.

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

Inductive unit_le : unit -> unit -> Prop :=
  | unit_le_refl : forall x, unit_le x x.

Lemma unit_le_trans : forall a b c,
  unit_le a b -> unit_le b c -> unit_le a c.
Proof.
  intros. destruct a, b, c. assumption.
Qed.

Instance preorder_unit : PreorderedSet unit :=
{
  preorder := unit_le;
  preorder_refl := unit_le_refl;
  preorder_trans := unit_le_trans;
}.

Inductive avalue_le : avalue -> avalue -> Prop :=
  | avalue_le_par : forall x y, 
      preorder x y -> avalue_le (VParity x) (VParity y)
  | avalue_le_bool : forall b c,
      preorder b c -> avalue_le (VAbstrBool b) (VAbstrBool c)
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
Qed.

Lemma avalue_le_refl : Reflexive avalue_le.
Proof. 
  unfold Reflexive. intro x. destruct x.
  - constructor. apply preorder_refl.
  - constructor. apply preorder_refl.
  - constructor.
  - constructor. 
Qed.

Global Instance avalue_preorder : PreorderedSet avalue :=
{
  preorder := avalue_le;
  preorder_refl := avalue_le_refl;
  preorder_trans := avalue_le_trans;
}.

Instance preordered_abstract_store : PreorderedSet abstract_store
:= {
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.
