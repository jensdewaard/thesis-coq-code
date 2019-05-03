Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses.

Class PreorderedSet (X : Type) : Type :=
{
  preorder : X -> X -> Prop;
  preorder_refl: Reflexive preorder;
  preorder_trans: Transitive preorder;
}.
Arguments Build_PreorderedSet X {_ _ _}.

Definition monotone {A A'} `{PreorderedSet A, PreorderedSet A'} :
  (A -> A') -> Prop :=
  fun f => forall (a a': A), preorder a a' -> preorder (f a) (f a').

Instance preorder_nat : PreorderedSet nat := 
{
  preorder := Nat.le;
  preorder_refl := Nat.le_refl;
  preorder_trans := Nat.le_trans;
}.

Inductive bool_le : bool -> bool -> Prop :=
  | bool_le_refl : forall b, bool_le b b.

Lemma bool_le_trans : Transitive bool_le.
Proof.
  unfold Transitive. intros. destruct x, y, z; try constructor; tauto.
Qed.

Instance preorder_bool : PreorderedSet bool :=
{
  preorder := bool_le;
  preorder_refl := bool_le_refl;
  preorder_trans := bool_le_trans;
}.

Section preordered_sets_le.
Context {A : Type}.

Inductive preordered_set_le : (A -> Prop) -> (A -> Prop) -> Prop := 
  | preordered_set_le_allin : forall (set1 set2 : (A -> Prop)),
      (forall (x : A), set1 x -> set2 x) -> preordered_set_le set1 set2.

Lemma preordered_set_le_refl : forall (a : (A->Prop)),
  preordered_set_le a a.
Proof.
  intros. constructor. intros. assumption.
Qed.

Lemma preordered_set_le_trans : forall (x y z : (A->Prop)),
  preordered_set_le x y -> preordered_set_le y z -> preordered_set_le x z.
Proof. 
  intros. constructor. inversion H; inversion H0; subst; auto.
Qed.

Global Instance types_to_prop : PreorderedSet (A -> Prop) :=
{
  preorder := preordered_set_le;
  preorder_refl := preordered_set_le_refl;
  preorder_trans := preordered_set_le_trans;
}.
End preordered_sets_le.
About types_to_prop.

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

About preordered_function_spaces.

Lemma preorder_props : forall {X : Type} (P Q : X -> Prop) (x : X),
  preorder P Q -> P x -> Q x.
Proof. 
  intros. simpl in H. destruct H. apply H. apply H0.
Qed.

Section preordered_options.
Context {A} `{PreorderedSet A}.

Inductive preordered_option_le :
  (option A) -> (option A) -> Prop :=
  | pre_opt_refl : forall o, preordered_option_le o o
  | pre_opt_none_some : forall (a : A), preordered_option_le (Some a) None
  | pre_opt_some_some : forall (a a' : A), 
      preorder a a' -> preordered_option_le (Some a) (Some a').

Lemma preordered_option_le_trans : 
  forall (a b c : option A),
  preordered_option_le a b -> preordered_option_le b c -> preordered_option_le
  a c.
Proof. 
  intros. induction H0.
  - assumption.
  - inversion H1; subst; constructor.
  - inversion H1; subst. 
    + constructor. assumption.
    + constructor. 
    + constructor. eapply preorder_trans.
      * apply H0.
      * apply H3.
Qed.

Global Instance preorder_option :
  PreorderedSet (option A). 
Proof.
  intros. esplit with (preorder := preordered_option_le).
  - (* reflexivity *) unfold Reflexive. apply pre_opt_refl.
  - (* transitivity *) unfold Transitive. apply preordered_option_le_trans.
Defined.

End preordered_options.

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
