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
Proof. intros. destruct ab1; destruct b1; inversion H.
  - simpl. assumption.
  - destruct ab2; try inversion H0; try reflexivity.
  - destruct ab2; try inversion H0; try reflexivity. 
    simpl. destruct b2; try reflexivity; try inversion H0.
  - destruct ab2; try reflexivity. inversion H0.
Qed.

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
Proof. intros. destruct ab1; destruct b1; inversion H.
  - destruct ab2; try reflexivity; try inversion H0.
  - simpl. assumption.
  - destruct ab2; try reflexivity; try inversion H0.
  - destruct ab2; try reflexivity. 
    + simpl. destruct b2; try reflexivity; try inversion H0.
    + inversion H0.
Qed.

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
Proof. intros. unfold sound_ab. 
  destruct ab, b; try inversion H; try reflexivity.
Qed.

