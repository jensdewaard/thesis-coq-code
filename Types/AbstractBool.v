Require Export Base.
Require Import Utf8 Coq.Bool.Bool Classes.IsBool Classes.PreorderedSet
  Classes.Joinable Classes.Galois.

(** * Definition *)

Definition abstr_bool' : Type := bool+⊤.

Inductive abstr_bool : Type :=
  | ab_true   : abstr_bool
  | ab_false  : abstr_bool.

(** * Correspondence with bool *)
Inductive gamma_bool : abstr_bool → bool → Prop :=
  | gamma_bool_true : ∀ P, P = true → gamma_bool ab_true P
  | gamma_bool_false : ∀ P, P = false → gamma_bool ab_false P.
Hint Constructors gamma_bool : soundness.

Instance galois_boolean : Galois abstr_bool bool := gamma_bool.
(** * Operations *)

(** ** And *)

Definition and_ab (b1 b2 : abstr_bool) : abstr_bool :=
  match b1 with
  | ab_true   => b2
  | ab_false  => ab_false
  end.
Instance and_ab_op : and_op abstr_bool abstr_bool := and_ab.
Instance and_ab_sound : and_op_sound abstr_bool bool.
Proof.
  intros ab1 ab2 b1 b2 H1 H2. destruct ab1, ab2, b1, b2; try constructor; 
  auto; gamma_destruct; eauto with soundness.
Qed.

(** ** Or *)

Definition or_ab (b1 b2 : abstr_bool) : abstr_bool :=
  match b1 with
  | ab_false  => b2
  | ab_true   => ab_true
  end.
Instance or_ab_op : or_op abstr_bool abstr_bool := or_ab.
Instance or_ab_sound : or_op_sound abstr_bool bool.
Proof.
  intros ab1 ab2 b1 b2 H1 H2. destruct ab1, ab2, b1, b2; auto; gamma_destruct;
  eauto with soundness.
Qed.

(** ** Negation *)
Definition neg_ab (b : abstr_bool) : abstr_bool :=
  match b with
  | ab_false => ab_true
  | ab_true  => ab_false
  end.
Instance neg_ab_op : neg_op abstr_bool abstr_bool := neg_ab.
Instance neg_ab_sound : neg_op_sound abstr_bool bool.
Proof.
  intros ab b H; destruct ab, b; constructor; gamma_destruct; 
  eauto with soundness.
Qed.

(** ** If *)
Instance if_ab_op {B} : if_op abstr_bool B := λ b : abstr_bool,
  λ p1 : B, λ p2 : B,
  match b with
  | ab_true => p1
  | ab_false => p2
  end.


Definition ab_le (a b : abstr_bool) : Prop := a = b.
Hint Unfold ab_le : preorders.

Instance preorder_ab : PreorderedSet abstr_bool.
Proof. proof_preorder ab_le. Defined.

Definition abstract_bool_join (b1 b2 : abstr_bool) : (abstr_bool+⊤) :=
  match b1, b2 with
  | ab_true, ab_true => NotTop ab_true
  | ab_false, ab_false => NotTop ab_false
  | _, _ => Top
  end.

Instance abstr_bool_joinable : Joinable abstr_bool (abstr_bool+⊤).
Proof.
  split with abstract_bool_join. destruct x, y; reflexivity.
Defined.

Instance preorder_boolean_sound : PreorderSound abstr_bool bool.
Proof.
  intros x y Hpre n Hgamma. destruct x, y; eauto with soundness; inversion
  Hpre.
Qed.

Instance join_boolean_sound : JoinableSound abstr_bool (abstr_bool+⊤) bool.
Proof.
  intros x y. destruct x, y; cbv; intros b H; destruct H; try assumption; 
  constructor.
Qed.

