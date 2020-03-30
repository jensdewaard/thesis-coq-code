Require Export Base.
Require Import Classes.PreorderedSet.
Require Import Classes.Monad.
Require Import Coq.Arith.Le.
Require Import Coq.Classes.RelationClasses.
Require Import Types.State.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Parity.
Require Import Types.Stores.

Hint Unfold Reflexive Transitive : soundness.
Hint Resolve le_trans : soundness.

Definition bot_le {A} `{PreorderedSet A} : (A+⊥) → (A+⊥) → Prop :=
  λ a, λ b, match a, b with
            | Bot, _ => True
            | _, Bot => False
            | NotBot x, NotBot y => x ⊑ y
            end.

Instance preorder_bot {A} `{PreorderedSet A} : PreorderedSet (A+⊥).
Proof.
  split with (preorder:=bot_le).
  - intro. destruct x. reflexivity. apply preorder_refl.
  - intros x y z Hxy Hyz. destruct x, y, z; simpl in *; try reflexivity;
    try contradiction. eapply preorder_trans. apply Hxy. assumption.
Defined.

Definition top_le {A} `{PreorderedSet A} : (A+⊤) → (A+⊤) → Prop :=
  λ a, λ b, match a, b with
            | _, Top => True
            | Top, _ => False
            | NotTop x, NotTop y => x ⊑ y
            end.

Instance preorder_top {A} `{PreorderedSet A} : PreorderedSet (A+⊤).
Proof.
  split with (preorder:=top_le).
  - intro. destruct x. reflexivity. apply preorder_refl.
  - intros x y z Hxy Hyz. destruct x, y, z; simpl in *; try reflexivity;
    try contradiction. eapply preorder_trans. apply Hxy. assumption.
Defined.

Global Instance preorder_nat : PreorderedSet nat := 
{
  preorder := le;
  preorder_refl := le_refl;
  preorder_trans := le_trans;
}.

Inductive ab_le : abstr_bool → abstr_bool → Prop :=
  | ab_le_top    : ∀ ab, ab_le ab ab_top
  | ab_le_true   : ab_le ab_true ab_true
  | ab_le_false  : ab_le ab_false ab_false.
Hint Constructors ab_le : soundness.

Lemma ab_le_refl : Reflexive ab_le.
Proof.
  unfold Reflexive. destruct x; auto with soundness.
Qed.

Lemma ab_le_trans : Transitive ab_le.
Proof. 
  unfold Transitive. intros x y z Hxy Hyz.
  destruct y; inv Hxy; inv Hyz; auto with soundness.
Qed.

Instance preorder_ab : PreorderedSet abstr_bool :=
{
  preorder := ab_le;
  preorder_refl := ab_le_refl;
  preorder_trans := ab_le_trans;
}.

Section preordered_functions.
  Context {A A' : Type} `{A_preorder : PreorderedSet A'}.

  Inductive pointwise_ordering : (A → A') → (A → A') → Prop :=
  | pointwise_cons : ∀ f g,  
      (∀ x, preorder (f x) (g x)) → pointwise_ordering f g.
  Hint Constructors pointwise_ordering : soundness.

  Lemma pointwise_ordering_refl : 
    Reflexive pointwise_ordering.
  Proof. 
    auto with soundness.
  Qed.

  Lemma pointwise_ordering_trans : 
    Transitive pointwise_ordering.
  Proof. 
    unfold Transitive. intros x y z Hxy Hyz. constructor.
    destruct Hxy, Hyz. intro x. eapply preorder_trans; auto.
  Qed.

  Global Instance preordered_function_spaces : 
  PreorderedSet (A->A') :=
  {
    preorder := pointwise_ordering;
    preorder_refl := pointwise_ordering_refl;
    preorder_trans := pointwise_ordering_trans;
  }.
End preordered_functions.
Hint Constructors pointwise_ordering : soundness.

Section preordered_pairs.
  Context {A B : Type} 
    `{A_preorder : PreorderedSet A, B_preorder : PreorderedSet B}.

  Inductive preorder_pair_le : prod A B → prod A B → Prop :=
    | preorder_pair_cons : ∀ a b c d,
        preorder a c → preorder b d → preorder_pair_le (a,b) (c,d).
  Hint Constructors preorder_pair_le : soundness.

  Lemma preorder_pair_le_refl :
    Reflexive preorder_pair_le.
  Proof. 
    eauto with soundness.
    unfold Reflexive. intro x. destruct x. constructor; auto with soundness.
  Qed.

  Lemma preorder_pair_le_trans :
    Transitive preorder_pair_le.
  Proof. 
    unfold Transitive. intros x y z Hxy Hyz.
    destruct x as [x1 x2], z as [z1 z2]. 
    destruct y as [y1 y2]. inv Hxy; inv Hyz; eauto with soundness.
  Qed.

  Global Instance preorder_pairs : 
  PreorderedSet (A * B)%type :=
  {
    preorder := preorder_pair_le;
    preorder_refl := preorder_pair_le_refl;
    preorder_trans := preorder_pair_le_trans;
  }.

  Lemma preorder_pair_spec : ∀ p q, ∃ a b c d,
    preorder p q <-> preorder (a, b) (c, d).
  Proof.
    intros. destruct p, q. exists a, b, a0, b0. reflexivity.
  Qed.
End preordered_pairs.
Hint Constructors preorder_pair_le : soundness.

Inductive interval_le : interval → interval → Prop :=
  | interva_le_cons : ∀ i j,
      preorder (min j) (min i) → preorder (max i) (max j) →
      interval_le i j.
Hint Constructors interval_le : soundness.

Lemma interval_le_refl : Reflexive interval_le.
Proof. simple_solve. Qed.

Lemma interval_le_trans : Transitive interval_le.
Proof. 
  unfold Transitive. intros x y z Hxy Hyz.
  inv Hxy. inv Hyz. constructor; pre_trans. 
Qed.

Global Instance preorder_interval : PreorderedSet interval :=
{
  preorder := interval_le;
  preorder_refl := interval_le_refl;
  preorder_trans := interval_le_trans;
}.

Inductive parity_le : parity → parity → Prop :=
  | par_le_top    : ∀ p, parity_le p par_top
  | par_le_refl   : ∀ p, parity_le p p.
Hint Constructors parity_le : soundness.

Lemma parity_le_trans : Transitive parity_le.
Proof.
  unfold Transitive. intros x y z Hxy Hyz.
  destruct x, y, z; inv Hxy; inv Hyz; auto with soundness.
Qed.

Global Instance proset_parity : PreorderedSet parity :=
{
  preorder := parity_le;
  preorder_refl := par_le_refl;
  preorder_trans := parity_le_trans;
}.

Definition unit_le (u v : unit) : Prop := True.
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

Inductive avalue_le : avalue → avalue → Prop :=
  | avalue_le_par : ∀ p q, preorder p q → avalue_le (VParity p) (VParity q)
  | avalue_le_ab  : ∀ a b, preorder a b → 
      avalue_le (VAbstrBool a) (VAbstrBool b)
  | avalue_le_i   : ∀ i j, preorder i j →
      avalue_le (VInterval i) (VInterval j)
  | avalue_le_top : ∀ a, avalue_le a VTop
  | avalue_le_bottom : ∀ a, avalue_le VBottom a.
Hint Constructors avalue_le : soundness.

Lemma avalue_le_trans : Transitive avalue_le.
Proof.
  intros x y z Hxy Hyz. 
  destruct y; inv Hxy; inv Hyz; eauto with soundness.
Qed.

Lemma avalue_le_refl : Reflexive avalue_le.
Proof. 
  unfold Reflexive. intro x. destruct x; auto with soundness.
Qed.

Global Instance avalue_preorder : PreorderedSet avalue :=
{
  preorder := avalue_le;
  preorder_refl := avalue_le_refl;
  preorder_trans := avalue_le_trans;
}.

Section preordered_sets_le.
  Context {A : Type}.

  Inductive preordered_set_le : (A → Prop) → (A → Prop) → Prop :=
    | preordered_set_le_cons : ∀ (s t : A → Prop),
        (∀ x, s x → t x) → preordered_set_le s t.
  Hint Constructors preordered_set_le : soundness.

  Lemma preordered_set_le_refl : Reflexive preordered_set_le. 
  Proof. auto with soundness. Qed.

  Lemma preordered_set_le_trans : Transitive preordered_set_le.
  Proof. 
    unfold Transitive. intros s t u Hst Htu. 
    inv Hst. inv Htu. auto with soundness.
  Qed.

  Global Instance types_to_prop : PreorderedSet (A -> Prop) :=
  {
    preorder := preordered_set_le;
    preorder_refl := preordered_set_le_refl;
    preorder_trans := preordered_set_le_trans;
  }.

End preordered_sets_le.
Hint Constructors preordered_set_le : soundness.

Instance preordered_abstract_store : PreorderedSet abstract_store
:= {
  preorder := pointwise_ordering;
  preorder_refl := pointwise_ordering_refl;
  preorder_trans := pointwise_ordering_trans;
}.

Section state_preorder.
  Context {S A : Type} 
    `{S_preorder : PreorderedSet S, A_preorder : PreorderedSet A}.
  
  Global Instance state_preorder : 
  PreorderedSet (State S A) :=
  {
    preorder := pointwise_ordering;
    preorder_refl := pointwise_ordering_refl;
    preorder_trans := pointwise_ordering_trans;
  }.
End state_preorder.

Section identity_preorder.
  Context {A} `{A_preorder : PreorderedSet A}.

  Definition identity_le (i1 i2 : Identity A) : Prop :=
    match i1, i2 with
    | identity a1, identity a2 => preorder a1 a2
    end.

  Lemma identity_le_trans : Transitive identity_le.
  Proof.
    unfold Transitive. intros. destruct x, y, z.
    simpl in *. pre_trans.
  Qed.

  Lemma identity_le_refl : Reflexive identity_le.
  Proof.
    unfold Reflexive. destruct x; simpl. apply preorder_refl.
  Qed.

  Global Instance identity_preorder : PreorderedSet (Identity A) :=
  {
    preorder_refl := identity_le_refl;
    preorder_trans := identity_le_trans;
  }.
End identity_preorder.

Section option_preorder.
  Context {A} `{A_preorder : PreorderedSet A}.

  Inductive option_le : option A → option A → Prop :=
    | option_le_none : ∀ m, option_le m None
    | option_le_just : ∀ x y, preorder x y → option_le (Some x) (Some y).
  Hint Constructors option_le : soundness.

  Lemma option_le_trans : Transitive option_le.
  Proof. 
    unfold Transitive. intros x y z Hxy Hyz. inv Hxy; inv Hyz;
    eauto with soundness.
  Qed.

  Lemma option_le_refl : Reflexive option_le.
  Proof. 
    unfold Reflexive. intro x. destruct x; auto with soundness.
  Qed.

  Global Instance option_preorder : PreorderedSet (option A) :=
  {
    preorder := option_le;
    preorder_trans := option_le_trans;
    preorder_refl := option_le_refl;
  }.
End option_preorder.
Hint Constructors option_le : soundness.

Section optionT_preorder.
  Context {A} `{A_preorder : PreorderedSet A}.
  Context {M : Type → Type} `{M_monad : Monad M,
                              M_preordered : ∀ B, PreorderedSet B →
                              PreorderedSet (M B)}.

  Global Instance optionT_preorder : PreorderedSet (optionT M A) :=
  {
    preorder := preorder;
    preorder_trans := preorder_trans;
    preorder_refl := preorder_refl;
  }.
End optionT_preorder.

Section optionA_preorder.
  Context {A : Type} `{A_preorder : PreorderedSet A}.

  Inductive optionA_le : optionA A → optionA A → Prop :=
    | optionA_le_none : optionA_le NoneA NoneA
    | optionA_le_none_justornone : ∀ y, optionA_le NoneA (SomeOrNoneA y)
    | optionA_le_just : ∀ x y, preorder x y → optionA_le (SomeA x) (SomeA y)
    | optionA_le_justornone_r : ∀ x y, preorder x y →
        optionA_le (SomeA x) (SomeOrNoneA y)
    | optionA_le_justornone : ∀ x y, preorder x y →
        optionA_le (SomeOrNoneA x) (SomeOrNoneA y).
  Hint Constructors optionA_le : soundness.

  Lemma optionA_le_trans : Transitive optionA_le.
  Proof.
    intros x y z Hxy Hyz.
    inv Hxy; inv Hyz; eauto with soundness.
  Qed.

  Lemma optionA_le_refl : Reflexive optionA_le.
  Proof. 
    intro x. destruct x; auto with soundness.
  Qed.

  Global Instance optionA_preorder : PreorderedSet (optionA A) :=
  {
    preorder := optionA_le;
    preorder_trans := optionA_le_trans;
    preorder_refl := optionA_le_refl;
  }.
End optionA_preorder.
Hint Constructors optionA_le : soundness.

Section optionAT_preorder.
  Context {A : Type} `{A_preorder : PreorderedSet A}.
  Context {M : Type -> Type} `{M_monad : Monad M,
                               M_preorder : ∀ B, PreorderedSet B →
                               PreorderedSet (M B)}.

  Global Instance optionAT_preorder : PreorderedSet (optionAT M A) :=
  {
    preorder := preorder;
    preorder_refl := preorder_refl;
    preorder_trans := preorder_trans;
  }.
End optionAT_preorder.

Section statet_preorder.
  Context {S A : Type} `{A_preorder : PreorderedSet A, S_preorder : PreorderedSet S}.
  Context {M : Type -> Type} `{M_preorder : ∀ B, PreorderedSet B → 
                                PreorderedSet (M (B))}.

  Global Instance statet_preorder : PreorderedSet (StateT S M A) :=
  {
    preorder := pointwise_ordering;
    preorder_refl := pointwise_ordering_refl;
    preorder_trans := pointwise_ordering_trans;
  }.
End statet_preorder.
