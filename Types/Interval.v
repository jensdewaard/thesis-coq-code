Require Import Types.AbstractBool.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.PeanoNat.

Definition interval := (nat * nat) % type.

Definition min (i : interval) : nat := 
  if (Nat.leb (fst i) (snd i)) then (fst i) else (snd i).
Definition max (i : interval) : nat := 
  if (Nat.leb (fst i) (snd i)) then (snd i) else (fst i).

Definition iplus (i1 i2 : interval) : interval := 
  ((min i1) + (min i2), (max i1) + (max i2)).

Definition imult (i1 i2 : interval) : interval :=
  ((min i1) * (min i2), (max i1) * (max i2)).

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

Require Import Coq.Arith.Le.
Lemma interval_increasing : forall i,
  min i <= max i.
Proof with auto with arith.
  destruct i as [n m]. unfold min, max. simpl.
  generalize dependent n.
  induction m...
  - intro n. induction n...
  - induction n... simpl. 
    destruct (Nat.leb n m) eqn:Hnm.
    apply le_n_S. apply Nat.leb_le. apply Hnm.
    constructor. apply Nat.leb_gt. apply Hnm.
Qed.

Lemma interval_min_l : forall i j : interval,
  min i <= max i + max j ->
  min (min i, max i + max j) = min i.
Proof.
  intros i j H. unfold min, max in *. 
  destruct (fst i <=? snd i) eqn:Hi; simpl;
  destruct (fst j <=? snd j) eqn:Hj; simpl.
  - destruct (fst i <=? snd i + snd j) eqn:Hplus; try reflexivity.
    apply Nat.leb_nle in Hplus. exfalso. apply Hplus. apply H.
  - destruct (fst i <=? snd i + fst j) eqn:Hplus; try reflexivity.
    apply Nat.leb_nle in Hplus. exfalso. apply Hplus. apply H.
  - destruct (snd i <=? fst i + snd j) eqn:Hplus; try reflexivity.
    apply Nat.leb_nle in Hplus. exfalso. apply Hplus. apply H.
  - destruct (snd i <=? fst i + fst j) eqn:Hplus; try reflexivity.
    apply Nat.leb_nle in Hplus. exfalso. apply Hplus. apply H.
Qed.

Lemma interval_min_plus : forall i j,
  min (iplus i j) = min i + min j.
Proof.
  destruct i as [li ui], j as [lj uj]. unfold iplus.
  assert (min (li, ui) + min(lj, uj) <= max(li,ui) + max(lj,uj)).
  { apply Coq.Arith.Plus.plus_le_compat; apply interval_increasing. }
  unfold min at 1. simpl. apply Nat.leb_le in H. rewrite H.
  reflexivity.
Qed.

Lemma interval_max_plus : forall i j,
  max (iplus i j) = max i + max j.
Proof.
  unfold iplus. intros i j.
  assert (min i + min j <= max i + max j).
  { apply Coq.Arith.Plus.plus_le_compat; apply interval_increasing. }
  unfold max at 1. simpl. apply Nat.leb_le in H. rewrite H.
  reflexivity.
Qed.

Lemma interval_min_refl : forall i,
  min (i,i) = i.
Proof.
  intro. unfold min. simpl. destruct (i <=? i); reflexivity.
Qed.

Lemma interval_max_refl : forall i,
  max (i,i) = i.
Proof.
  intro. unfold max. simpl. destruct (i <=? i); reflexivity.
Qed.

Lemma interval_min_mult : forall i j,
  min (imult i j) = min i * min j.
Proof. 
  intros. unfold imult.
  assert (min i * min j <= max i * max j).
  apply Coq.Arith.Mult.mult_le_compat; apply interval_increasing.
  unfold min at 1. simpl. apply Nat.leb_le in H. rewrite H. reflexivity.
Qed.

Lemma interval_max_mult : forall i j,
  max (imult i j) = max i * max j.
Proof. 
  intros. unfold imult. assert (min i * min j <= max i * max j).
  apply Coq.Arith.Mult.mult_le_compat; apply interval_increasing.
  unfold max at 1. simpl. apply Nat.leb_le in H. rewrite H. reflexivity.
Qed.


