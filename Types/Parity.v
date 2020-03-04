Require Export Base.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.
Require Import Coq.Sets.Partial_Order.
Require Import Types.AbstractBool.

(** * Parity *)

Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity
  | par_top : parity.

Inductive parity_ensemble : parity -> Prop :=
  | par_ens_all : forall p, parity_ensemble p.

(** ** Operations *)

(** *** Plus *)
Definition parity_plus (p q : parity) : parity :=
  match p with 
  | par_top => match q with
               | _ => par_top
               end
  | par_even => q
  | par_odd => match q with
               | par_top => par_top
               | par_even => par_odd
               | par_odd => par_even
               end
  end.
Hint Unfold parity_plus : soundness.

Lemma parity_plus_par_even : forall p,
  parity_plus p par_even = p.
Proof. intros. destruct p; reflexivity. Qed.

Corollary parity_plus_par_odd : forall p,
  parity_plus p par_odd = par_even -> p = par_odd.
Proof.
  intros; destruct p; try inv H; reflexivity.
Qed.

Lemma parity_plus_assoc : forall p q r,
  parity_plus (parity_plus p q) r = parity_plus p (parity_plus q r).
Proof.
  destruct p, q, r; try reflexivity.
Qed.

Lemma parity_plus_comm : forall p q,
  parity_plus p q = parity_plus q p.
Proof.
  destruct p, q; try reflexivity. 
Qed.

Definition parity_mult (p q : parity) : parity :=
  match p with
  | par_even => par_even
  | par_odd => q
  | par_top => par_top
  end.
Hint Unfold parity_mult : soundness.

(** Equality *)
Definition parity_eq (p1 p2 : parity) : abstr_bool :=
  match p1, p2 with
  | par_even, par_odd => ab_false
  | par_odd, par_even => ab_false
  | _, _ => ab_top
  end.

Definition parity_leb (p1 p2 : parity) : abstr_bool :=
  match p1, p2 with
  | _, par_top    => ab_true
  | par_even, par_odd | par_odd, par_even => ab_top
  | par_even, par_even | par_odd, par_odd => ab_top
  | par_top, _  => ab_top
  end.

(* Some lemmas regarding Nat.Even and Nat.Odd that are missing but are included
 * for the deprecated even and odd. We define these lemmas here so we can use the  * newer definitions for when the older version are deleted. *)
Lemma Even_add : forall n m, Nat.Even n -> Nat.Even m -> Nat.Even (n + m).
Proof.
  intros. rewrite <- Nat.even_spec in *. 
  replace true with (Bool.eqb (Nat.even n) (Nat.even m)).
  apply Nat.even_add. rewrite H, H0. reflexivity.
Qed.

Lemma Odd_Odd_add : forall n m, Nat.Odd n -> Nat.Odd m -> Nat.Even (n + m).
Proof.
  intros. rewrite <- even_equiv. 
  rewrite <- odd_equiv in H, H0. apply odd_even_plus; assumption.
Qed.

Lemma Odd_Even_add : forall n m, Nat.Odd n -> Nat.Even m -> Nat.Odd (n + m).
Proof.
  intros. rewrite <- even_equiv in H0. rewrite <- odd_equiv in H.
  rewrite <- odd_equiv. apply odd_plus_l; assumption.
Qed.

Lemma Even_Odd_add : forall n m, Nat.Even n -> Nat.Odd m -> Nat.Odd (n + m).
Proof.
  intros. rewrite <- even_equiv in H. rewrite <- odd_equiv in H0.
  rewrite <- odd_equiv. apply odd_plus_r; assumption.
Qed.

Lemma Even_mult_l : forall n m, Nat.Even n -> Nat.Even (n * m).
Proof.
  intros. rewrite <- even_equiv in *. apply even_mult_l. assumption.
Qed.

Lemma Even_mult_r : forall n m, Nat.Even m -> Nat.Even (n * m).
Proof.
  intros. rewrite <- even_equiv in *. apply even_mult_r; assumption.
Qed.

Lemma Odd_mult : forall n m, Nat.Odd n -> Nat.Odd m -> Nat.Odd (n * m).
Proof.
  intros. rewrite <- odd_equiv in *. apply odd_mult; assumption.
Qed.

Hint Resolve Even_add Odd_Odd_add Odd_Even_add Even_Odd_add : soundness.
Hint Resolve Even_mult_l Even_mult_r Odd_mult : soundness.
Hint Resolve Nat.Even_Odd_False : soundness. 
