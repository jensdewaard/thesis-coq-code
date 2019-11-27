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

Definition gamma_par (p : parity) (n : nat) : Prop :=
  match p with
  | par_even => Nat.Even n
  | par_odd => Nat.Odd n
  | par_top => True
  | par_false => False
  end. 
Hint Unfold gamma_par : soundness.

Lemma gamma_par_monotone : monotone gamma_par.
Proof. simple_solve. Qed.

Instance galois_parity_nat : Galois nat parity :=
{
  gamma := gamma_par;
  gamma_monotone := gamma_par_monotone;
}.

Definition gamma_interval (i : interval) (n : nat) : Prop :=
  preorder (min i) n /\ preorder n (max i).
Hint Unfold gamma_interval : soundness.

Lemma gamma_interval_monotone : monotone gamma_interval.
Proof. simple_solve. Qed.

Instance  galois_interval : Galois nat interval :=
{
  gamma := gamma_interval;
  gamma_monotone := gamma_interval_monotone;
}.

Definition gamma_bool (a : abstr_bool) (b : bool) : Prop :=
  match a, b with
  | ab_true, true
  | ab_false, false
  | ab_top, _ => True
  | _, _ => False
  end.
Hint Unfold gamma_bool : soundness.

Lemma gamma_bool_monotone : monotone gamma_bool.
Proof.
  simple_solve.
Qed.

Instance galois_boolean : Galois bool abstr_bool :=
{
  gamma := gamma_bool;
  gamma_monotone := gamma_bool_monotone;
}.

Section galois_functions.
Context {A A' B B' : Type} 
  `{Galois B A, Galois B' A'}.

Definition gamma_fun (f : A -> A') (g : B -> B') : Prop :=
  forall a b, gamma a b -> gamma (f a) (g b).
Hint Unfold gamma_fun : soundness. 

Lemma gamma_fun_monotone :
  monotone gamma_fun.
Proof.
  simple_solve.
  apply widen with (f:= a a0). apply H3. auto.
Qed.

Global Instance GFun : 
  Galois (B -> B') (A->A') :=
{
  gamma := gamma_fun;
  gamma_monotone := gamma_fun_monotone;
}.

End galois_functions.
Hint Unfold gamma_fun : soundness.

Section galois_values.

Definition gamma_value (a : avalue) (c : cvalue) : Prop :=
  match a, c with
  | VParity p, VNat n => gamma p n
  | VInterval i, VNat n => gamma i n
  | VAbstrBool ab, VBool b => gamma ab b
  | VTop, _ => True
  | _, _ => False
  end.
Hint Unfold gamma_value : soundness.

Lemma gamma_value_monotone : monotone gamma_value.
Proof.
  simple_solve. 
Qed.

Global Instance galois_values : Galois cvalue avalue := 
{
  gamma := gamma_value;
  gamma_monotone := gamma_value_monotone;
}.
End galois_values.
Hint Unfold gamma_value : soundness.

Definition gamma_store (st' : abstract_store) (st : store) : Prop :=
  forall x, gamma (st' x) (st x).
Hint Unfold gamma_store : soundness.

Lemma gamma_store_monotone : monotone gamma_store.
Proof. unfold monotone. intros ast ast' H. simpl in *.
  unfold pointwise_ordering, preordered_set_le in *. intros st Hgamma.
  unfold gamma_store in *. intro x. eapply widen.
  apply H. apply Hgamma.
Qed.

Global Instance galois_store : Galois store abstract_store :=
{
  gamma := gamma_store;
  gamma_monotone := gamma_store_monotone;
}.

Section galois_pairs.
Context {A B C D} `{Galois B A} `{Galois D C}.

Definition gamma_pairs (p : prod A C) (q : prod B D) : Prop :=
  let (a, c) := p in let (b, d) := q in gamma a b /\ gamma c d.
Hint Unfold gamma_pairs : soundness.

Lemma gamma_pairs_monotone :
  monotone gamma_pairs.
Proof.
  simple_solve; apply_widen.
Qed.

Global Instance galois_pairs :
  Galois (B*D) (A*C) :=
{
  gamma := gamma_pairs;
  gamma_monotone := gamma_pairs_monotone;
}.
End galois_pairs.
Hint Unfold gamma_pairs : soundness.

Section galois_maybe.
  Context {A A'} `{Galois A A'}.

  Definition gamma_maybeA (am : AbstractMaybe A') (m : Maybe A) : Prop :=
    match am, m with
    | NoneA, _ 
    | JustOrNoneA _, None => True
    | JustA x, Just y
    | JustOrNoneA x, Just y => gamma x y
    | _, _ => False
    end.
  Hint Unfold gamma_maybeA : soundness.

  Definition gamma_maybe (m : Maybe A') (n : Maybe A) : Prop :=
    match m, n with
    | None, _ => True
    | Just x, Just y => gamma x y
    | _, _ => False
    end.
  Hint Unfold gamma_maybe : soundness.

  Lemma gamma_maybeA_monotone : monotone gamma_maybeA.
  Proof.
    simple_solve; apply_widen.
  Qed.

  Lemma gamma_maybe_monotone : monotone gamma_maybe.
  Proof.
    simple_solve; apply_widen.
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
Hint Unfold gamma_maybeA gamma_maybe : soundness.

Section galois_state.
Context {A A'} 
  `{Galois A A'}.

Global Instance galois_state :
  Galois (ConcreteState A) (AbstractState A') :=
  {
    gamma := gamma_fun;
    gamma_monotone := gamma_fun_monotone;
  }.
End galois_state.

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
  Context {A A' : Type} `{PreorderedSet (MaybeT M' A')}.
  Context {M_has_galois : Galois (M (Maybe A)) (M' (Maybe A'))}.

  Global Instance galois_maybeT : Galois (MaybeT M A) (MaybeT M' A') :=
  {
    gamma := gamma (Galois:=(M_has_galois));
    gamma_monotone := gamma_monotone;
  }.
End galois_maybeT.
