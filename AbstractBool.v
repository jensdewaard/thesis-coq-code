Require Import Coq.Bool.Bool.

(** * Definition *)

Inductive abstr_bool : Type :=
  | ab_true   : abstr_bool
  | ab_false  : abstr_bool
  | ab_top    : abstr_bool
  | ab_bottom : abstr_bool.

(** * Correspondence with bool *)

Inductive ab_le : abstr_bool -> abstr_bool -> Prop :=
  | ab_le_bottom : forall ab, ab_le ab_bottom ab
  | ab_le_top : forall ab, ab_le ab ab_top
  | ab_le_refl : forall ab, ab_le ab ab.

Lemma ab_le_trans :forall a b c,
  ab_le a b -> ab_le b c -> ab_le a c.
Proof. 
  intros. destruct a, b, c; try constructor; try inversion H0; try inversion H.
Qed.

Definition gamma_bool (ab: abstr_bool) (b : bool) : Prop :=
  match ab with
  | ab_true   => Is_true b
  | ab_false  => ~Is_true b
  | ab_top    => True
  | ab_bottom => False
  end.

Definition extract_bool (b: bool) : abstr_bool :=
  match b with
  | true => ab_true
  | false => ab_false
  end.

Definition sound_ab (ab: abstr_bool) (b: bool) := gamma_bool ab b.

(** * Operations *)

(** ** And *)

Definition and_ab (b1 b2 : abstr_bool) : abstr_bool :=
  match b1 with
  | ab_bottom => ab_bottom
  | ab_true   => b2
  | ab_top    => match b2 with
                 | ab_bottom => ab_bottom
                 | ab_false  => ab_false
                 | _         => ab_top
                 end
  | ab_false  => match b2 with
                 | ab_bottom => ab_bottom
                 | _ => ab_false
                 end
  end.

Example and_ab1 : and_ab ab_bottom ab_top = ab_bottom. reflexivity. Qed.
Example and_ab2 : and_ab ab_true ab_true = ab_true. reflexivity. Qed.
Example and_ab3 : and_ab ab_true ab_false = ab_false. reflexivity. Qed.
Example and_ab4 : and_ab ab_top  ab_true = ab_top. reflexivity. Qed.

Lemma and_ab_comm : forall b1 b2, and_ab b1 b2 = and_ab b2 b1.
Proof. destruct b1, b2; reflexivity. Qed.

Lemma and_ab_assoc : forall b1 b2 b3, 
  and_ab (and_ab b1 b2) b3 = and_ab b1 (and_ab b2 b3).
Proof. destruct b1, b2, b3; reflexivity. Qed.

Lemma and_ab_sound : forall ab1 ab2 b1 b2,
  sound_ab ab1 b1 ->
  sound_ab ab2 b2 ->
  sound_ab (and_ab ab1 ab2) (andb b1 b2).
Proof. destruct ab1, b1, ab2, b2; simpl; tauto. Qed.

(** ** Or *)

Definition or_ab (b1 b2 : abstr_bool) : abstr_bool :=
  match b1 with
  | ab_bottom => ab_bottom
  | ab_false  => b2
  | ab_top    => match b2 with
                 | ab_bottom => ab_bottom
                 | ab_true   => ab_true
                 | _         => ab_top
                 end
  | ab_true   => match b2 with
                 | ab_bottom => ab_bottom
                 | _         => ab_true
                 end
  end.

Lemma or_ab_comm : forall b1 b2, or_ab b1 b2 = or_ab b2 b1.
Proof. intros. destruct b1, b2; reflexivity. Qed.

Lemma or_ab_assoc : forall b1 b2 b3,
  or_ab (or_ab b1 b2) b3 = or_ab b1 (or_ab b2 b3).
Proof. intros. destruct b1, b2, b3; reflexivity. Qed.

Lemma or_ab_sound : forall ab1 ab2 b1 b2,
  sound_ab ab1 b1 ->
  sound_ab ab2 b2 ->
  sound_ab (or_ab ab1 ab2) (orb b1 b2).
Proof. destruct ab1, b1, ab2, b2; simpl; tauto. Qed.

(** ** Negation *)
Definition neg_ab (b : abstr_bool) : abstr_bool :=
  match b with
  | ab_false => ab_true
  | ab_true  => ab_false
  | _ => b
  end.

Lemma neg_ab_involutive : forall ab, neg_ab (neg_ab ab) = ab.
Proof. destruct ab; reflexivity. Qed.

Lemma neg_ab_injective : forall ab1 ab2, neg_ab ab1 = neg_ab ab2 -> ab1 = ab2.
Proof. intros. destruct ab1, ab2; try reflexivity; try inversion H. Qed.

Lemma neg_ab_sound : forall ab b,
  sound_ab ab b ->
  sound_ab (neg_ab ab) (negb b).
Proof. destruct ab, b; simpl; tauto. Qed.

(** ** Join *)
Definition ab_join (ab1 ab2 : abstr_bool) : abstr_bool :=
  match ab1, ab2 with
  | ab_bottom, b | b, ab_bottom => b
  | ab_top, _ | _, ab_top => ab_top
  | ab_true, ab_true => ab_true
  | ab_false, ab_false => ab_false
  | ab_true, ab_false | ab_false, ab_true => ab_top
  end.

Lemma ab_join_comm : forall (ab1 ab2 : abstr_bool),
  ab_join ab1 ab2 = ab_join ab2 ab1.
Proof. 
  intros. destruct ab1, ab2; auto. 
Qed.

Lemma ab_join_assoc : forall (ab1 ab2 ab3 : abstr_bool),
  ab_join ab1 (ab_join ab2 ab3) = ab_join (ab_join ab1 ab2) ab3.
Proof. 
  intros. destruct ab1, ab2, ab3; auto.
Qed.

Lemma ab_join_idem : forall ab,
  ab_join ab ab = ab.
Proof. 
  intros. destruct ab; auto.
Qed.

(** ** Meet *)
Definition ab_meet (ab1 ab2 : abstr_bool) : abstr_bool :=
  match ab1, ab2 with
  | ab_bottom, _ | _, ab_bottom => ab_bottom
  | ab_top, b | b, ab_top => b
  | ab_true, ab_true => ab_true
  | ab_false, ab_false => ab_false
  | ab_true, ab_false | ab_false, ab_true => ab_bottom
  end.


Lemma ab_meet_assoc : forall (ab1 ab2 : abstr_bool),
  ab_meet ab1 ab2 = ab_meet ab2 ab1.
Proof. 
  intros. destruct ab1, ab2; auto.
Qed.

Lemma ab_meet_idem : forall ab,
  ab_meet ab ab = ab.
Proof. 
  intros. destruct ab; auto. 
Qed.
