Require Import Classes.Applicative.
Require Export Base.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Le.
Require Import Coq.Classes.RelationClasses.
Require Import Instances.Monad.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Parity.
Require Import Types.Result.
Require Import Types.Stores.

Hint Unfold Reflexive Transitive : soundness.
Hint Resolve le_trans : soundness.

Global Instance preorder_nat : PreorderedSet nat := 
{
  preorder := le;
  preorder_refl := le_refl;
  preorder_trans := le_trans;
}.

Definition ab_le (a b : abstr_bool) : Prop :=
  match a with
  | ab_bottom => True
  | ab_top => match b with
              | ab_top => True
              | _ => False
              end
  | ab_true => match b with
               | ab_true | ab_top => True
               | ab_false | ab_bottom => False
               end
  | ab_false => match b with
                | ab_false | ab_top => True
                | ab_true  | ab_bottom => False
                end
  end.
Hint Unfold ab_le : soundness.

Lemma ab_le_refl : Reflexive ab_le.
Proof.
  simple_solve. 
Qed.

Lemma ab_le_trans : Transitive ab_le.
Proof. 
  simple_solve. 
Qed.

Instance preorder_ab : PreorderedSet abstr_bool :=
{
  preorder := ab_le;
  preorder_refl := ab_le_refl;
  preorder_trans := ab_le_trans;
}.

Section preordered_functions.
  Context {A A' : Type} `{PreorderedSet A'}.

  Definition pointwise_ordering (f g : A -> A') : Prop :=
    forall x, preorder (f x) (g x).
  Hint Unfold pointwise_ordering : soundness.

  Lemma pointwise_ordering_refl : 
    Reflexive pointwise_ordering.
  Proof.  
    simple_solve. 
  Qed.

  Lemma pointwise_ordering_trans : 
    Transitive pointwise_ordering.
  Proof.
    simple_solve.
  Qed.

  Global Instance preordered_function_spaces : 
  PreorderedSet (A->A') :=
  {
    preorder := pointwise_ordering;
    preorder_refl := pointwise_ordering_refl;
    preorder_trans := pointwise_ordering_trans;
  }.
End preordered_functions.
Hint Unfold pointwise_ordering : soundness.

Section preordered_pairs.
  Context {A B : Type} `{PreorderedSet A, PreorderedSet B}.

  Definition preorder_pair_le (p1 p2 : prod A B) : Prop :=
    let (a, b) := p1 in let (c, d) := p2 in
    preorder a c /\ preorder b d.
  Hint Unfold preorder_pair_le : soundness.

  Lemma preorder_pair_le_refl :
    Reflexive preorder_pair_le.
  Proof. 
    simple_solve. 
  Qed.

  Lemma preorder_pair_le_trans :
    Transitive preorder_pair_le.
  Proof. 
    simple_solve. 
  Qed.

  Global Instance preorder_pairs : 
  PreorderedSet (A * B)%type :=
  {
    preorder := preorder_pair_le;
    preorder_refl := preorder_pair_le_refl;
    preorder_trans := preorder_pair_le_trans;
  }.
End preordered_pairs.
Hint Unfold preorder_pair_le : soundness.

Definition interval_le (i j : interval) : Prop := 
  preorder (min j) (min i) /\ preorder (max i) (max j).
Hint Unfold interval_le : soundness.

Lemma interval_le_refl : Reflexive interval_le.
Proof.
  simple_solve. 
Qed.

Lemma interval_le_trans : Transitive interval_le.
Proof.
  simple_solve. 
Qed.

Global Instance preorder_interval : PreorderedSet interval :=
{
  preorder := interval_le;
  preorder_refl := interval_le_refl;
  preorder_trans := interval_le_trans;
}.

Definition parity_le (p q : parity) : Prop :=
  match p with
  | par_bottom => True
  | p' => q = p'
  end.
Hint Unfold parity_le : soundness.

Lemma parity_le_refl : Reflexive parity_le.
Proof. simple_solve. Qed.

Lemma parity_le_trans : Transitive parity_le.
Proof.
  simple_solve. 
Qed.

Global Instance proset_parity : PreorderedSet parity :=
{
  preorder := parity_le;
  preorder_refl := parity_le_refl;
  preorder_trans := parity_le_trans;
}.

Definition unit_le (u v : unit) : Prop := u = v.
Hint Unfold unit_le : soundness.

Lemma unit_le_refl : Reflexive unit_le.
Proof. simple_solve. Qed.

Lemma unit_le_trans : Transitive unit_le.
Proof. simple_solve. Qed.

Instance preorder_unit : PreorderedSet unit :=
{
  preorder := unit_le;
  preorder_refl := unit_le_refl;
  preorder_trans := unit_le_trans;
}.

Definition avalue_le (v w : avalue) : Prop :=
  match v, w with
  | VParity x, VParity y => preorder x y
  | VAbstrBool b, VAbstrBool c => preorder b c
  | VInterval i, VInterval j => preorder i j
  | _, VTop => True
  | VBottom, _ => True
  | _, _ => False
  end.
Hint Unfold avalue_le : soundness.

Lemma avalue_le_trans : Transitive avalue_le.
Proof.
  intros x y z Hxy Hyz. destruct x, y, z; unfold avalue_le in *; try pre_trans;
  try inversion Hyz; try inversion Hxy; try reflexivity.
Qed.

Lemma avalue_le_refl : Reflexive avalue_le.
Proof. 
  simple_solve.
Qed.

Global Instance avalue_preorder : PreorderedSet avalue :=
{
  preorder := avalue_le;
  preorder_refl := avalue_le_refl;
  preorder_trans := avalue_le_trans;
}.


Section preordered_sets_le.
  Context {A : Type}.

  Definition preordered_set_le (set1 set2 : A -> Prop) : Prop :=
    forall x, set1 x -> set2 x.
  Hint Unfold preordered_set_le : soundness.

  Lemma preordered_set_le_refl : Reflexive preordered_set_le. 
  Proof. simple_solve. Qed.

  Lemma preordered_set_le_trans : Transitive preordered_set_le.
  Proof. simple_solve. Qed.

  Global Instance types_to_prop : PreorderedSet (A -> Prop) :=
  {
    preorder := preordered_set_le;
    preorder_refl := preordered_set_le_refl;
    preorder_trans := preordered_set_le_trans;
  }.

End preordered_sets_le.
Hint Unfold preordered_set_le : soundness.

Instance preordered_abstract_store : PreorderedSet abstract_store
:= {
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.

Section state_preorder.
  Context {S A : Type} `{PreorderedSet S, PreorderedSet A}.
  
  Global Instance state_preorder : 
  PreorderedSet (State S A) :=
  {
    preorder := pointwise_ordering;
    preorder_refl := pointwise_ordering_refl;
    preorder_trans := pointwise_ordering_trans;
  }.
End state_preorder.

Section maybe_preorder.
  Context {A} `{PreorderedSet A}.

  Definition maybe_le (m n : Maybe A) : Prop :=
    match m, n with
    | _, None => True
    | None, Just _ => False
    | Just x, Just y => preorder x y
    end.
  Hint Unfold maybe_le : soundness.

  Lemma maybe_le_trans : Transitive maybe_le.
  Proof. simple_solve. Qed.

  Lemma maybe_le_refl : Reflexive maybe_le.
  Proof. simple_solve. Qed.

  Global Instance maybe_preorder : PreorderedSet (Maybe A) :=
  {
    preorder := maybe_le;
    preorder_trans := maybe_le_trans;
    preorder_refl := maybe_le_refl;
  }.
End maybe_preorder.
Hint Unfold maybe_le : soundness.

Section maybea_preorder.
  Context {A : Type} `{PreorderedSet A}.

  Definition maybea_le (m n : AbstractMaybe A) : Prop :=
    match m, n with
    | _, NoneA => True
    | JustA x, JustA y
    | JustA x, JustOrNoneA y
    | JustOrNoneA x, JustOrNoneA y => preorder x y
    | _, _ => False
    end.
  Hint Unfold maybea_le : soundness.

  Lemma maybea_le_trans : Transitive maybea_le.
  Proof.
    intros x y z Hxy Hyz. destruct x, y, z; simpl in *;
    try pre_trans; try reflexivity;
      try inv Hxy; try inv Hyz.
  Qed.

  Lemma maybea_le_refl : Reflexive maybea_le.
  Proof. 
    simple_solve.
  Qed.

  Global Instance maybea_preorder : PreorderedSet (AbstractMaybe A) :=
  {
    preorder := maybea_le;
    preorder_trans := maybea_le_trans;
    preorder_refl := maybea_le_refl;
  }.
End maybea_preorder.
Hint Unfold maybea_le : soundness.

Section maybeAT_preorder.
  Context {A : Type} `{PreorderedSet A}.
  Context {M : Type -> Type} `{inst : Monad} 
    {M_preserves_order : forall A, PreorderedSet A -> PreorderedSet (M A)}.

  Global Instance maybeat_preorder : PreorderedSet (MaybeAT M A) :=
  {
    preorder := preorder (X:=(M (AbstractMaybe A)));
    preorder_refl := preorder_refl;
    preorder_trans := preorder_trans;
  }.

End maybeAT_preorder.

Section statet_preorder.
  Context {S A : Type}.
  Context {M : Type -> Type} `{PreorderedSet (M (A*S)%type)}.
  Global Instance statet_preorder : PreorderedSet (StateT S M A) :=
  {
    preorder := pointwise_ordering;
    preorder_refl := pointwise_ordering_refl;
    preorder_trans := pointwise_ordering_trans;
  }.
End statet_preorder.

