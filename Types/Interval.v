Require Export Base.
Require Import Arith.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Plus.
Require Import Psatz.
Require Import Types.AbstractBool.
From Coq Require Export EqdepFacts.

Record interval := Interval {
  min: nat;
  max : nat;
  min_max : min <= max;
}.

Notation "[ x , y ]" := (@Interval x y _).

Lemma nat_le_pi : ∀ x y (H1 H2 : x ≤ y), H1 = H2.
Proof.
  assert (∀ x y (p : x ≤ y) y' (q : x ≤ y'),
  y = y' → eq_dep nat (le x) y p y' q) as aux.
  { fix FIX 3. intros x ? [|y p] ? [|y' q].
  - constructor.
  - clear FIX. intros; exfalso; lia.
  - clear FIX. intros; exfalso; lia.
  - injection 1. intros Hy. case (FIX x
    y p y' q Hy); constructor. }
  intros x y p q.
  apply (Eqdep_dec.eq_dep_eq_dec eq_nat_dec), aux.
  reflexivity.
Qed.

Lemma plus_min_max : ∀ i1 i2, 
  min i1 + min i2 ≤ max i1 + max i2.
Proof.
  destruct i1, i2; simpl. lia.
Qed.

Lemma interval_eq i1 i2 j1 j2 H1 H2 :
     i1 = i2 → j1 = j2 →
        Interval i1 j1 H1 = Interval i2 j2 H2.
Proof. 
  intros -> ->. 
  f_equal. apply nat_le_pi. 
Qed.

Definition iplus (i1 i2 : interval) : interval := 
  Interval ((min i1) + (min i2)) ((max i1) + (max i2)) (plus_min_max i1 i2).
Hint Unfold iplus : soundness.

Lemma mult_min_max : ∀ i1 i2,
  min i1 * min i2 ≤ max i1 * max i2.
Proof.
  destruct i1, i2; simpl. 
  apply Nat.mul_le_mono; assumption.
Qed.

Definition imult (i1 i2 : interval) : interval :=
  Interval ((min i1) * (min i2)) ((max i1) * (max i2)) (mult_min_max i1 i2).
Hint Unfold imult : soundness.

Definition ieqb (i1 i2 : interval) : abstr_bool :=
  if (Nat.ltb (max i1) (min i2)) then
    ab_false
  else if (andb (andb (Nat.eqb (min i1) (max i1)) 
                      (Nat.eqb (max i1) (min i2))) 
                (Nat.eqb (min i2) (max i2))) then
           ab_true
  else ab_top.

Definition ileqb (i1 i2 : interval) : abstr_bool :=
  if (Nat.ltb (max i1) (min i2)) then
    ab_true
  else if (Nat.ltb (max i2) (min i1)) then
    ab_false
  else
    ab_top.

Lemma interval_min_mult : forall i j,
  min (imult i j) = min i * min j.
Proof. 
  intros. unfold imult. simpl. reflexivity.
Qed.

Lemma interval_max_mult : forall i j,
  max (imult i j) = max i * max j.
Proof. 
  intros. unfold imult. simpl. reflexivity.
Qed.
