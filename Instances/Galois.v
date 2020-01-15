Require Export Base.
Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Bool.Bool.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Parity.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

Inductive gamma_par : parity → nat → Prop :=
  | gamma_par_even : ∀ n, Nat.Even n → gamma_par par_even n
  | gamma_par_odd  : ∀ n, Nat.Odd n → gamma_par par_odd n
  | gamma_par_top  : ∀ n, gamma_par par_top n.
Hint Constructors gamma_par : soundness.

Lemma gamma_par_monotone : monotone gamma_par.
Proof. 
  unfold monotone. intros a a' Hpre. constructor.
  intros n Hgamma. inv Hgamma; inv Hpre; eauto with soundness.
Qed.

Instance galois_parity_nat : Galois nat parity :=
{
  gamma := gamma_par;
  gamma_monotone := gamma_par_monotone;
}.

Inductive gamma_interval : interval → nat → Prop :=
  | gamma_interval_cons : ∀ i n, 
      preorder (min i) n → preorder n (max i) → gamma_interval i n.
Hint Constructors gamma_interval : soundness.

Lemma gamma_interval_monotone : monotone gamma_interval.
Proof. 
  unfold monotone. intros. constructor. intros.
  inv H0; inv H; eauto with soundness.
Qed.

Instance  galois_interval : Galois nat interval :=
{
  gamma := gamma_interval;
  gamma_monotone := gamma_interval_monotone;
}.

Inductive gamma_bool : abstr_bool → bool → Prop :=
  | gamma_bool_true : ∀ P, P = true → gamma_bool ab_true P
  | gamma_bool_false : ∀ P, P = false → gamma_bool ab_false P
  | gamma_bool_top : ∀ b, gamma_bool ab_top b.
Hint Constructors gamma_bool : soundness.

Lemma gamma_bool_monotone : monotone gamma_bool.
Proof.
  constructor. intros. inv H0; inv H; eauto with soundness.
Qed.

Instance galois_boolean : Galois bool abstr_bool :=
{
  gamma := gamma_bool;
  gamma_monotone := gamma_bool_monotone;
}.

Section galois_functions.
Context {A A' B B' : Type}  `{Galois A A', Galois B B'}.

Inductive gamma_fun : (A' → B') → (A → B) → Prop :=
  | gamma_fun_cons : ∀ (f : A' → B') (g : A → B), 
      (∀ (a : A) (a' : A'),
      gamma a' a → gamma (f a') (g a)) → gamma_fun f g.

  Lemma gamma_fun_monotone :
    monotone gamma_fun.
  Proof.
    constructor. intros. inv H2; inv H1. 
    constructor. intros. eapply widen; eauto. 
  Qed.

  Global Instance GFun : 
  Galois (A → B) (A' → B') :=
  {
    gamma := gamma_fun;
    gamma_monotone := gamma_fun_monotone;
  }.
End galois_functions.
Hint Constructors gamma_fun : soundness.

Section galois_values.
  Inductive gamma_value : avalue → cvalue → Prop :=
    | gamma_value_parity : ∀ p n, gamma p n → gamma_value (VParity p) (VNat n)
    | gamma_value_interval : ∀ i n, 
        gamma i n → gamma_value (VInterval i) (VNat n)
    | gamma_value_bool : ∀ ab b,
        gamma ab b → gamma_value (VAbstrBool ab) (VBool b)
    | gamma_value_top : ∀ v, gamma_value VTop v.
  Hint Constructors gamma_value : soundness.

  Lemma gamma_value_monotone : monotone gamma_value.
  Proof.
    constructor. intros v Hgamma. inv Hgamma; inv H; eauto with soundness.
    constructor. apply_widen.
    constructor. apply_widen.
    constructor. apply_widen.
  Qed.

  Global Instance galois_values : Galois cvalue avalue := 
  {
    gamma := gamma_value;
    gamma_monotone := gamma_value_monotone;
  }.
End galois_values.
Hint Constructors gamma_value : soundness.

Inductive gamma_store : abstract_store → store → Prop :=
  | gamma_store_cons : ∀ st' st, 
      (∀ x, gamma (st' x) (st x)) → gamma_store st' st.
Hint Constructors gamma_store : soundness.

Lemma gamma_store_monotone : monotone gamma_store.
Proof. 
  constructor. intros x Hgamma. inv Hgamma; inv H. 
  constructor. intros. eapply widen. apply H1.
  apply H0.
Qed.

Global Instance galois_store : Galois store abstract_store :=
{
  gamma := gamma_store;
  gamma_monotone := gamma_store_monotone;
}.

Section galois_pairs.
  Context {A A' B B'} `{Galois A A'} `{Galois B B'}.

  Inductive gamma_pairs : prod A' B' → prod A B → Prop :=
    | gamma_pairs_cons : ∀ (p : (A'*B')%type) (q : (A*B)%type), 
        gamma (fst p) (fst q) → gamma (snd p) (snd q) → gamma_pairs p q.

  Lemma gamma_pairs_monotone :
    monotone gamma_pairs.
  Proof.
    constructor. intros. inv H2; inv H1. destruct x.
    simpl in H4. simpl in H3.
    constructor; simpl; apply_widen. 
  Qed.

  Global Instance galois_pairs :
  Galois (A*B) (A'*B') :=
  {
    gamma := gamma_pairs;
    gamma_monotone := gamma_pairs_monotone;
  }.
End galois_pairs.
Hint Constructors gamma_pairs : soundness.

Section galois_maybe.
  Context {A A'} `{Galois A A'}.

  Inductive gamma_maybeA : AbstractMaybe A' → Maybe A → Prop :=
    | gamma_noneA : ∀ m, gamma_maybeA NoneA m
    | gamma_justornoneA_none : ∀ a, 
        gamma_maybeA (JustOrNoneA a) None
    | gamma_justA_just : ∀ a' a, gamma a' a → gamma_maybeA (JustA a') (Just a)
    | gamma_justornone_just : ∀ a' a, 
        gamma a' a →
        gamma_maybeA (JustOrNoneA a') (Just a).
  Hint Constructors gamma_maybeA : soundness.

  Inductive gamma_maybe : Maybe A' → Maybe A → Prop :=
    | gamma_none : ∀ m, gamma_maybe None m
    | gamma_just_just : ∀ a' a, gamma a' a → gamma_maybe (Just a') (Just a).
  Hint Constructors gamma_maybe : soundness.

  Lemma gamma_maybeA_monotone : monotone gamma_maybeA.
  Proof.
    unfold monotone. intros. constructor. intros.
    inv H0; inv H1; try constructor; apply_widen.
  Qed.

  Lemma gamma_maybe_monotone : monotone gamma_maybe.
  Proof.
    unfold monotone. intros. constructor. intros.
    inv H0; inv H1; try constructor; apply_widen.
  Qed.

  Global Instance galois_maybeA : Galois (Maybe A) (AbstractMaybe A') :=
  {
    gamma := gamma_maybeA;
    gamma_monotone := gamma_maybeA_monotone;
  }.

  Global Instance galois_maybe : Galois (Maybe A) (Maybe A') :=
  {
    gamma := gamma_maybe;
    gamma_monotone := gamma_maybe_monotone;
  }.
End galois_maybe.
Hint Constructors gamma_maybeA gamma_maybe : soundness.

Section galois_unit.
  Definition gamma_unit (u v : unit) : Prop := True.

  Lemma gamma_unit_monotone : monotone gamma_unit.
  Proof. constructor. reflexivity. Qed.

  Global Instance galois_unit : Galois unit unit := 
  {
    gamma := gamma_unit;
    gamma_monotone := gamma_unit_monotone;
  }. 
End galois_unit.
Hint Unfold gamma_unit : soundness.

Section galois_maybeT.
  Context {A A' : Type} `{Galois A A'}.
  Context {M M' : Type → Type} `{Monad M, Monad M'}
    {M_galois : ∀ T T', Galois T T' → Galois (M T) (M' T')}.

  Global Instance galois_maybeT : Galois (MaybeT M A) (MaybeT M' A') :=
  {
    gamma := gamma (Galois:=M_galois (Maybe A) (Maybe A') _);
    gamma_monotone := gamma_monotone;
  }.
End galois_maybeT.

Section galois_maybeAT.
  Context {A A' : Type} `{Galois A A'}.
  Context {M M' : Type → Type} `{Monad M, Monad M'} 
    {M_galois : ∀ T T', Galois T T' → Galois (M T) (M' T')}.

  Global Instance galois_maybeAT : Galois (MaybeT M A) (MaybeAT M' A') :=
  {
    gamma := gamma (Galois:=M_galois (Maybe A) (AbstractMaybe A') _);
    gamma_monotone := gamma_monotone;
  }.
End galois_maybeAT.

Section galois_stateT.
  Context {A A': Type} `{Galois A A'}.
  Context {S S' : Type} {M M' : Type → Type} `{Galois S S'} 
    `{Monad M, Monad M'} {M_galois : ∀ A A', Galois A A' → Galois (M A) (M' A')}.

  Global Instance galois_stateT : Galois (StateT S M A) (StateT S' M' A') :=
  {
    gamma := gamma_fun;
    gamma_monotone := gamma_fun_monotone;
  }.
End galois_stateT.

Instance galois_state_monad (S S' : Type) `{Galois S S'} 
  (A A' : Type) `{Galois A A'} : Galois (State S A) (State S' A') :=
  {
    gamma := gamma_fun;
    gamma_monotone := gamma_fun_monotone;
  }.

Section galois_state.
  Context {A A' B B'} `{Galois A A', Galois B B'}.

  Definition gamma_abstract_state : AbstractState A' → ConcreteState A → Prop
    := gamma_fun.

  Definition gamma_abstract_state_monotone : monotone gamma_abstract_state.
  Proof.
    unfold gamma_abstract_state. apply gamma_fun_monotone.
  Qed.

  Global Instance galois_state : Galois (ConcreteState A) (AbstractState A') 
  := {
    gamma := gamma_fun;
    gamma_monotone := gamma_fun_monotone;
  }.
End galois_state.
