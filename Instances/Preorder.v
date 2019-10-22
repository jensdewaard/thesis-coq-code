Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Le.
Require Import Coq.Classes.RelationClasses.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Parity.
Require Import Types.Result.
Require Import Types.Stores.

Global Instance preorder_nat : PreorderedSet nat := 
{
  preorder := le;
  preorder_refl := le_refl;
  preorder_trans := le_trans;
}.


Inductive ab_le : abstr_bool -> abstr_bool -> Prop :=
  | ab_le_bottom : forall ab, ab_le ab_bottom ab
  | ab_le_top : forall ab, ab_le ab ab_top
  | ab_le_refl : forall ab, ab_le ab ab.

Lemma ab_le_trans :forall a b c,
  ab_le a b -> ab_le b c -> ab_le a c.
Proof. 
  intros. destruct a, b, c; try constructor; try inversion H0; 
  try inversion H.
Qed.

Instance preorder_ab : PreorderedSet abstr_bool :=
{
  preorder := ab_le;
  preorder_refl := ab_le_refl;
  preorder_trans := ab_le_trans;
}.


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

Inductive interval_le : interval -> interval -> Prop :=
  | interval_le_shorter : forall i i', 
      preorder (min i') (min i) -> preorder (max i) (max i') -> interval_le i i'.

Lemma interval_le_refl : Reflexive interval_le.
Proof.
  unfold Reflexive. intro x. destruct x as [n m].
  constructor; apply preorder_refl.
Qed.

Lemma interval_le_trans : Transitive interval_le.
Proof.
  unfold Transitive. intros i j k Hij Hjk. inversion Hij; subst; clear Hij;
  inversion Hjk; subst; clear Hjk. constructor.
  - eapply preorder_trans. apply H1. apply H.
  - eapply preorder_trans. apply H0. apply H2.
Qed.

Global Instance preorder_interval : PreorderedSet interval :=
{
  preorder := interval_le;
  preorder_refl := interval_le_refl;
  preorder_trans := interval_le_trans;
}.

Inductive parity_le : parity -> parity -> Prop :=
  | lt_top : forall p, parity_le p par_top
  | lt_bottom : forall p, parity_le par_bottom p
  | lt_refl : forall p, parity_le p p.

Lemma parity_le_refl : forall p, parity_le p p.
destruct p; constructor. Qed.

Lemma parity_le_trans : forall p1 p2 p3,
  parity_le p1 p2 -> parity_le p2 p3 -> parity_le p1 p3.
destruct p1, p2, p3; intros; try constructor; 
  try inversion H; try inversion H0. Qed.

Global Instance proset_parity : PreorderedSet parity :=
{
  preorder := parity_le;
  preorder_refl := parity_le_refl;
  preorder_trans := parity_le_trans;
}.

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

Instance preordered_abstract_store : PreorderedSet abstract_store
:= {
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.

Section result_preorder.
Context {A S: Type} `{PreorderedSet A, PreorderedSet S}.

Inductive result_le : abstract_result A S -> abstract_result A S -> Prop :=
  | result_le_crashed : forall r, result_le r (crashedA )
  | result_le_exception : forall s1 s2, 
      preorder s1 s2 -> result_le (exceptionA s1) (exceptionA s2)
  | result_le_return : forall a1 a2 s1 s2, 
      preorder a1 a2 -> 
      preorder s1 s2 ->
      result_le (returnRA a1 s1) (returnRA a2 s2)
  | result_le_exception_or : forall a st1 st2, 
      preorder st1 st2 -> 
      result_le (exceptionA st1) (exceptionOrReturn a st2)
  | result_le_return_or : forall a1 a2 s1 s2,
      preorder s1 s2 ->
      preorder a1 a2 ->
      result_le (returnRA a1 s1) (exceptionOrReturn a2 s2)
  | result_le_or_or : forall a1 a2 s1 s2,
      preorder a1 a2 ->
      preorder s1 s2 ->
      result_le (exceptionOrReturn a1 s1) (exceptionOrReturn a2 s2).

Lemma result_le_refl :
  Reflexive result_le.
Proof.
  unfold Reflexive. destruct x; try constructor; try apply preorder_refl.
Qed.

Lemma result_le_trans :
  Transitive result_le.
Proof.
  unfold Transitive.
  intros x y z H1 H2.
  inversion H1; inversion H2; subst; 
  try constructor; try inversion H2; subst; auto; eapply preorder_trans;
  try apply H3; try apply H4; auto.
Qed.

Global Instance result_preorder : PreorderedSet (abstract_result A S) := {
  preorder := result_le;
  preorder_refl := result_le_refl;
  preorder_trans := result_le_trans;
}.
End result_preorder.

