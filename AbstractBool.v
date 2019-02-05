Require Import Coq.Bool.Bool.

(** * Definition *)

Inductive abstr_bool : Type :=
  | ab_true   : abstr_bool
  | ab_false  : abstr_bool
  | ab_top    : abstr_bool
  | ab_bottom : abstr_bool.

Definition Is_false (b: bool) :=
  match b with
  | true => False
  | false => True
  end.

Definition Is_bool (b: bool) := True.
Definition No_bool (b: bool) := False.

(** * Correspondence with bool *)

Definition gamma_bool (ab: abstr_bool) : (bool -> Prop) :=
  match ab with
  | ab_true   => Is_true
  | ab_false  => Is_false
  | ab_top    => Is_bool
  | ab_bottom => No_bool
  end.

Definition extract_bool (b: bool) : abstr_bool :=
  match b with
  | true => ab_true
  | false => ab_false
  end.

(** * Operations *)

(** ** And *)

Definition and_ab (b1 b2 : abstr_bool) : abstr_bool :=
  match b1, b2 with
  | ab_bottom, _         => ab_bottom
  | _        , ab_bottom => ab_bottom
  | ab_false , _         => ab_false
  | _        , ab_false  => ab_false
  | ab_top   , ab_true   => ab_top
  | ab_true  , ab_top    => ab_top
  | ab_top   , ab_top    => ab_top
  | ab_true  , ab_true   => ab_true
  end.

Lemma and_ab_comm : forall b1 b2, and_ab b1 b2 = and_ab b2 b1.
Proof. destruct b1, b2; reflexivity. Qed.

Lemma and_ab_assoc : forall b1 b2 b3, 
  and_ab (and_ab b1 b2) b3 = and_ab b1 (and_ab b2 b3).
Proof. destruct b1, b2, b3; reflexivity. Qed.

Lemma and_ab_trans : forall b1 b2 b3,
  and_ab b1 b2 = ab_true -> and_ab b2 b3 = ab_true -> and_ab b1 b3 = ab_true.
Proof.
  intros. destruct b1, b2, b3; try reflexivity; try inversion H0; try inversion
  H.
Qed.

(** ** Or *)

Definition or_ab (b1 b2 : abstr_bool) : abstr_bool :=
  match b1, b2 with
  | ab_bottom, _ => ab_bottom
  | _, ab_bottom => ab_bottom
  | ab_true, _   => ab_true
  | _ , ab_true  => ab_true
  | ab_top, ab_false => ab_top
  | ab_false, ab_top => ab_top
  | ab_top, ab_top  => ab_top
  | ab_false, ab_false => ab_false
  end.

Lemma or_ab_comm : forall b1 b2, or_ab b1 b2 = or_ab b2 b1.
Proof. intros. destruct b1, b2; reflexivity. Qed.

Lemma or_ab_assoc : forall b1 b2 b3,
  or_ab (or_ab b1 b2) b3 = or_ab b1 (or_ab b2 b3).
Proof. intros. destruct b1, b2, b3; reflexivity. Qed.


