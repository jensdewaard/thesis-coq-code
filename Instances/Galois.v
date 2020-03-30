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
Require Import Types.Stores.
Require Import Types.State.

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
  γ := gamma_par;
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
  gamma_monotone := gamma_bool_monotone;
}.

Section galois_functions.
Context {A A' B B' : Type}  `{A_galois : Galois A A', B_galois : Galois B B'}.

Inductive gamma_fun : (A' → B') → (A → B) → Prop :=
  | gamma_fun_cons : ∀ (f : A' → B') (g : A → B), 
      (∀ (a : A) (a' : A'),
      γ a' a → γ (f a') (g a)) → gamma_fun f g.

  Lemma gamma_fun_monotone :
    monotone gamma_fun.
  Proof.
    unfold monotone. intros f f' Hf.
    constructor. intros x Hx.
    constructor. intros a a' Ha. 
    inversion Hf as [? ? Hfx]; subst.
    inversion Hx as [?]; subst.
    apply (gamma_preorder (f a')); auto. 
  Qed.

  Global Instance GFun : 
  Galois (A → B) (A' → B') :=
  {
    gamma_monotone := gamma_fun_monotone;
  }.
End galois_functions.
Hint Constructors gamma_fun : soundness.

Section galois_values.
  Inductive gamma_value : avalue → cvalue → Prop :=
    | gamma_value_parity : ∀ p n, γ p n → gamma_value (VParity p) (VNat n)
    | gamma_value_interval : ∀ i n, 
        γ i n → gamma_value (VInterval i) (VNat n)
    | gamma_value_bool : ∀ ab b,
        γ ab b → gamma_value (VAbstrBool ab) (VBool b)
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
    gamma_monotone := gamma_value_monotone;
  }.
End galois_values.
Hint Constructors gamma_value : soundness.

Inductive gamma_store : abstract_store → store → Prop :=
  | gamma_store_cons : ∀ st' st, 
      (∀ x, γ (st' x) (st x)) → gamma_store st' st.
Hint Constructors gamma_store : soundness.

Lemma gamma_store_monotone : monotone gamma_store.
Proof. 
  constructor. intros x Hgamma. inv Hgamma; inv H. 
  constructor. intros. eapply gamma_preorder; auto.
Qed.

Global Instance galois_store : Galois store abstract_store :=
{
  gamma_monotone := gamma_store_monotone;
}.

Section galois_pairs.
  Context {A A' B B'} `{A_galois : Galois A A'} `{B_galois : Galois B B'}.

  Inductive gamma_pairs : prod A' B' → prod A B → Prop :=
    | gamma_pairs_cons : ∀ (p : (A'*B')%type) (q : (A*B)%type), 
        γ (fst p) (fst q) → γ (snd p) (snd q) → gamma_pairs p q.

  Lemma gamma_pairs_monotone :
    monotone gamma_pairs.
  Proof.
    unfold monotone. intros f f' Hf.
    constructor. intros p Hfp.
    inversion Hf as [a b c d Hac Hbd]; subst.
    inversion Hfp as [? ? Hfp1 Hfp2];subst. destruct p as [a' b'].
    constructor; simpl in *; apply_widen.
  Qed.

  Global Instance galois_pairs :
  Galois (A*B) (A'*B') :=
  {
    gamma_monotone := gamma_pairs_monotone;
  }.
End galois_pairs.
Hint Constructors gamma_pairs : soundness.

Section galois_identity.
  Context {A A'} `{A_galois : Galois A A'}.

  Definition gamma_identity (ia' : Identity A') 
                            (ia : Identity A) : Prop :=
    match ia', ia with
    | identity a', identity a => γ a' a
    end.

  Lemma gamma_identity_monotone : monotone gamma_identity. 
  Proof.
    unfold monotone. intros ia ia' Hpre. simpl.
    constructor. intros x Hx.  destruct ia, ia', x. simpl in *.
    apply_widen.
  Qed.

  Global Instance galois_identity : Galois (Identity A) (Identity A') :=
  {
    gamma_monotone := gamma_identity_monotone;
  }.
End galois_identity.

Section galois_option.
  Context {A A'} `{A_galois : Galois A A'}.

  Inductive gamma_optionA : optionA A' → option A → Prop :=
    | gamma_noneA : gamma_optionA NoneA None
    | gamma_SomeornoneA_none : ∀ a, 
        gamma_optionA (SomeOrNoneA a) None
    | gamma_SomeA_Some : ∀ a' a, γ a' a → gamma_optionA (SomeA a') (Some a)
    | gamma_Someornone_Some : ∀ a' a, 
        γ a' a →
        gamma_optionA (SomeOrNoneA a') (Some a).
  Hint Constructors gamma_optionA : soundness.

  Inductive gamma_option : option A' → option A → Prop :=
    | gamma_none : ∀ m, gamma_option None m
    | gamma_Some_Some : ∀ a' a, γ a' a → gamma_option (Some a') (Some a).
  Hint Constructors gamma_option : soundness.

  Lemma gamma_optionA_monotone : monotone gamma_optionA.
  Proof.
    unfold monotone. intros a a' Ha. constructor; intros m Hm.
    inv Ha; inv Hm; eauto with soundness; try constructor; try apply_widen.
  Qed.

  Lemma gamma_option_monotone : monotone gamma_option.
  Proof.
    unfold monotone. intros a a' Ha. constructor; intros m Hm.
    inv Ha; inv Hm; eauto with soundness. constructor. apply_widen.
  Qed.

  Global Instance galois_optionA : Galois (option A) (optionA A') :=
  {
    gamma_monotone := gamma_optionA_monotone;
  }.

  Global Instance galois_option : Galois (option A) (option A') :=
  {
    gamma_monotone := gamma_option_monotone;
  }.
End galois_option.
Hint Constructors gamma_optionA gamma_option : soundness.

Section galois_unit.
  Definition gamma_unit (u v : unit) : Prop := True.

  Lemma gamma_unit_monotone : monotone gamma_unit.
  Proof. constructor. reflexivity. Qed.

  Global Instance galois_unit : Galois unit unit := 
  {
    gamma_monotone := gamma_unit_monotone;
  }. 
End galois_unit.
Hint Unfold gamma_unit : soundness.

Section galois_optionT.
  Context {A A' : Type} `{A_galois : Galois A A'}.
  Context {M M' : Type → Type} `{M_monad : Monad M, M'_monad : Monad M'}
    {M_preorderset : ∀ B, PreorderedSet B → PreorderedSet (M B)}
    {M'_preorderset : ∀ B, PreorderedSet B → PreorderedSet (M' B)}
    {M_galois : ∀ (T T' : Type) {HT : PreorderedSet T'} 
      {HM : PreorderedSet (M' T')}, 
      @Galois T T' HT → @Galois (M T) (M' T') HM}.

  Global Instance galois_optionT : Galois (optionT M A) (optionT M' A') :=
  {
    gamma_monotone := gamma_monotone;
  }.
End galois_optionT.

Section galois_optionAT.
  Context {A A' : Type} `{A_galois : Galois A A'}.
  Context {M M' : Type → Type} `{M_monad : Monad M, M'_monad : Monad M'} 
    {M_preorderset : ∀ B, PreorderedSet B → PreorderedSet (M B)}
    {M'_preorderset : ∀ B, PreorderedSet B → PreorderedSet (M' B)}
    {M_galois : ∀ (T T' : Type) {HT : PreorderedSet T'} 
      {HM : PreorderedSet (M' T')}, 
      @Galois T T' HT → @Galois (M T) (M' T') HM}.

  Global Instance galois_optionAT : Galois (optionT M A) (optionAT M' A') :=
  {
    gamma_monotone := gamma_monotone;
  }.
End galois_optionAT.

Section galois_stateT.
  Context {A A': Type} `{A_galois : Galois A A'}.
  Context {S S' : Type} {M M' : Type → Type} `{S_galois : Galois S S'} 
    `{M_monad : Monad M, M'_monad : Monad M'} 
    {M_galois : ∀ (T T' : Type) {HT : PreorderedSet T'} 
      {HM : PreorderedSet (M' T')}, 
      @Galois T T' HT → @Galois (M T) (M' T') HM}.
  Context {HMpre: PreorderedSet (M' (A' * S')%type)}.

  Global Instance galois_stateT : Galois (StateT S M A) (StateT S' M' A') :=
  {
    gamma_monotone := gamma_fun_monotone;
  }.
End galois_stateT.

Instance galois_state_monad (S S' : Type) `{S_galois : Galois S S'} 
  (A A' : Type) `{A_galois : Galois A A'} : Galois (State S A) (State S' A') :=
  {
    gamma_monotone := gamma_fun_monotone;
  }.
