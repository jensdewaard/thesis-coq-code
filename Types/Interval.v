Require Export Base.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Plus.
Require Import Omega.
Require Import Types.AbstractBool.

Definition interval := (nat * nat) % type.

Definition min (i : interval) : nat := Nat.min (fst i) (snd i).
  (*if (Nat.leb (fst i) (snd i)) then (fst i) else (snd i).*)
Definition max (i : interval) : nat := Nat.max (fst i) (snd i).
  (*if (Nat.leb (fst i) (snd i)) then (snd i) else (fst i).*)

Definition iplus (i1 i2 : interval) : interval := 
  ((min i1) + (min i2), (max i1) + (max i2)).
Hint Unfold iplus : soundness.

Definition imult (i1 i2 : interval) : interval :=
  ((min i1) * (min i2), (max i1) * (max i2)).
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

Lemma interval_increasing : forall i,
  min i <= max i.
Proof with auto with arith.
  destruct i as [n m]. unfold min, max. simpl. 
  eapply Nat.le_trans. apply Nat.le_min_l. apply Nat.le_max_l.
Qed.

Lemma interval_min_l : forall i : interval,
  (*min i <= max i + max j ->*)
  min (min i, max i) = min i.
Proof.
  intros i. 
  unfold min, max in *; simpl. 
  omega with *.
Qed.
Hint Rewrite interval_min_l : soundness.

Lemma interval_min_Nat_min : ∀ i j,
  (min (Nat.min (min i) (min j), Nat.max (max i) (max j))) =
  Nat.min (min i) (min j).
Proof.
  intros. unfold min, max. simpl. omega with *.
Qed.

Lemma interval_max_Nat_max : ∀ i j,
  (max (Nat.min (min i) (min j),
        Nat.max (max i) (max j))) = Nat.max (max i) (max j).
Proof.
  intros. unfold min, max. simpl. omega with *.
Qed.

Lemma interval_min_plus : forall i j,
  min (iplus i j) = min i + min j.
Proof.
  destruct i as [li ui], j as [lj uj]. unfold iplus.
  assert (min (li, ui) + min(lj, uj) <= max(li,ui) + max(lj,uj)).
  { apply Coq.Arith.Plus.plus_le_compat; apply interval_increasing. }
  unfold min, max in *. simpl. apply Nat.leb_le in H. omega with *.
Qed.

Lemma interval_max_plus : forall i j,
  max (iplus i j) = max i + max j.
Proof.
  unfold iplus. intros i j.
  assert (min i + min j <= max i + max j).
  { apply Coq.Arith.Plus.plus_le_compat; apply interval_increasing. }
  unfold max at 1. simpl. apply Nat.leb_le in H. unfold min, max in *.
  omega with *.
Qed.

Lemma interval_min_refl : forall i,
  min (i,i) = i.
Proof.
  intro. unfold min. simpl. rewrite Nat.min_id. reflexivity.
Qed.
Hint Rewrite interval_min_refl : soundness.

Lemma interval_max_refl : forall i,
  max (i,i) = i.
Proof.
  intro. unfold max. simpl. rewrite Nat.max_id; reflexivity.
Qed.
Hint Rewrite interval_max_refl : soundness.

Lemma interval_min_mult : forall i j,
  min (imult i j) = min i * min j.
Proof. 
  intros. unfold imult.
  assert (min i * min j <= max i * max j).
  apply Coq.Arith.Mult.mult_le_compat; apply interval_increasing.
  unfold min, max in *. simpl. omega with *.
Qed.

Lemma interval_max_mult : forall i j,
  max (imult i j) = max i * max j.
Proof. 
  intros. unfold imult. assert (min i * min j <= max i * max j).
  apply Coq.Arith.Mult.mult_le_compat; apply interval_increasing.
  unfold min, max in *. simpl. omega with *.
Qed.
