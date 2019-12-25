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
Context {A A' B B' : Type} 
  `{Galois B A, Galois B' A'}.

Inductive gamma_fun : (A → A') → (B → B') → Prop :=
  | gamma_fun_cons : ∀ (f : A → A') (g : B → B'), 
      (∀ a b, gamma a b → gamma (f a) (g b)) → gamma_fun f g.
Hint Constructors gamma_fun : soundness. 

Lemma gamma_fun_monotone :
  monotone gamma_fun.
Proof.
  constructor. intros. inv H2; inv H1. 
  constructor. intros.  eapply widen; eauto. 
Qed.

Global Instance GFun : 
  Galois (B -> B') (A->A') :=
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
Context {A B C D} `{Galois B A} `{Galois D C}.

Inductive gamma_pairs : prod A C → prod B D → Prop :=
  | gamma_pairs_cons : ∀ (p : (A*C)%type) (q : (B*D)%type), 
      gamma (fst p) (fst q) → gamma (snd p) (snd q) → gamma_pairs p q.

Lemma gamma_pairs_monotone :
  monotone gamma_pairs.
Proof.
  constructor. intros. inv H2; inv H1. destruct x.
  simpl in H4. simpl in H3.
  constructor; simpl; apply_widen. 
Qed.

Global Instance galois_pairs :
  Galois (B*D) (A*C) :=
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

  Global Instance galois_maybe_maybeA : Galois (Maybe A) (AbstractMaybe A') :=
  {
    gamma := gamma_maybeA;
    gamma_monotone := gamma_maybeA_monotone;
  }.

  Global Instance galois_maybe_maybe : Galois (Maybe A) (Maybe A') :=
  {
    gamma := gamma_maybe;
    gamma_monotone := gamma_maybe_monotone;
  }.
End galois_maybe.
Hint Constructors gamma_maybeA gamma_maybe : soundness.


Section galois_unit.
  Definition gamma_unit (u v : unit) : Prop := True.

Lemma gamma_unit_monotone : monotone gamma_unit.
Proof. simple_solve. Qed.

Global Instance galois_unit : Galois unit unit := 
{
  gamma := gamma_unit;
  gamma_monotone := gamma_unit_monotone;
}. 
End galois_unit.
Hint Unfold gamma_unit : soundness.

Section galois_maybeT.
  Context {M M' : Type → Type} `{Monad M, Monad M'}.
  Hypothesis M_galois : ∀ A A', Galois A A' → Galois (M A) (M' A').

  Global Instance galois_maybeT {A A'} `{Galois A A'} : 
    Galois (MaybeT M A) (MaybeT M' A') := {
    gamma := gamma (Galois:=M_galois (Maybe A) (Maybe A') galois_maybe_maybe);
    gamma_monotone := gamma_monotone;
  }.
End galois_maybeT.

Section galois_maybeAT.
  Context {M M' : Type → Type} `{Monad M, Monad M'}.
  Hypothesis M_galois : ∀ A A', Galois A A' → Galois (M A) (M' A').
  
  Global Instance galois_maybeAT {A A'} `{Galois A A'} :
    Galois (MaybeT M A) (MaybeAT M' A') := {
      gamma := gamma (Galois:=M_galois (Maybe A) (AbstractMaybe A')
      galois_maybe_maybeA);
      gamma_monotone := gamma_monotone;
    }.
End galois_maybeAT.

Section galois_stateT.
  Context {M M' : Type → Type}.
  Hypothesis M_galois : ∀ A A', Galois A A' → Galois (M A) (M' A').

  Instance galois_stateT {S S' A A'} `{Galois S S', Galois A A'} :
    Galois (StateT S M A) (StateT S' M' A') :=
  {
    gamma := gamma_fun;
    gamma_monotone := gamma_fun_monotone;
  }.
End galois_stateT.

Instance galois_state_monad {S S' A A' : Type} `{Galois S S', Galois A A'} :
  Galois (State S A) (State S' A') :=
  {
    gamma := gamma_fun;
    gamma_monotone := gamma_fun_monotone;
  }.

Section galois_state.
Context {A A'} `{Galois A A'}.

Global Instance galois_state :
  Galois (ConcreteState A) (AbstractState A') :=
  {
    gamma := gamma (Galois:=GFun);
  }.
  Proof.
    unfold monotone. repeat constructor. intros. 
    inv H0. eapply widen. apply H3. destruct H2.
    destruct H1. eauto with soundness.
  Defined.
End galois_state.
