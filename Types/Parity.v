Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.
Require Import Coq.Sets.Partial_Order.

Require Import Types.AbstractBool.

(** * Parity *)

Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity
  | par_top : parity
  | par_bottom : parity.

Inductive parity_ensemble : parity -> Prop :=
  | par_ens_all : forall p, parity_ensemble p.

(** ** Operations *)

(** *** Plus *)
Definition parity_plus (p q : parity) : parity :=
  match p with 
  | par_top => match q with
               | par_bottom => par_bottom
               | _ => par_top
               end
  | par_even => q
  | par_odd => match q with
               | par_top => par_top
               | par_even => par_odd
               | par_odd => par_even
               | par_bottom => par_bottom
               end
  | par_bottom => par_bottom
  end.

Lemma parity_plus_par_even : forall p,
  p = parity_plus p par_even.
Proof.
  destruct p; reflexivity.
Qed.

Corollary parity_plus_par_odd : forall p,
  parity_plus p par_odd = par_even -> p = par_odd.
Proof. 
  intros. destruct p; try reflexivity; try inversion H.
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
  | par_bottom => par_bottom
  end.


(** Equality *)
Definition parity_eq (p1 p2 : parity) : abstr_bool :=
  match p1, p2 with
  | par_even, par_odd => ab_false
  | par_odd, par_even => ab_false
  | par_bottom, _ | _, par_bottom => ab_bottom
  | _, _ => ab_top
  end.


