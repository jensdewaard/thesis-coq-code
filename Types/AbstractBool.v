Require Export Base.
Require Import Utf8 Coq.Bool.Bool Classes.IsBool Classes.PreorderedSet
  Classes.Joinable Classes.Galois.

(** * Definition *)

Definition abstr_bool : Type := bool+⊤.

(** * Correspondence with bool *)
Instance galois_boolean : Galois abstr_bool bool := 
  λ ab,
    match ab with
    | Top => λ _, True
    | NotTop b => λ b', b = b'
    end.
(** * Operations *)

(** extract *)
Instance extract_ab : extract_op bool abstr_bool := λ b, NotTop b.

Instance extract_ab_sound : extract_op_sound extract_ab extract_bool.
Proof.
  intro b. destruct b; constructor; reflexivity.
Qed.
Hint Resolve extract_ab_sound : soundness.
  
(** ** And *)
Instance and_ab_op : and_op abstr_bool := 
  λ ab1 ab2,
    match ab1, ab2 with
    | Top, _ | _, Top => Top
    | NotTop b1, NotTop b2 => NotTop (andb b1 b2)
    end.

Instance and_ab_sound : and_op_sound and_ab_op and_op_bool.
Proof.
  intros ab1 ab2 b1 b2 H1 H2. destruct ab1, ab2, b1, b2; try constructor; 
  auto; gamma_destruct; eauto with soundness.
Qed.
Hint Resolve and_ab_sound : soundness.

(** ** Or *)
Instance or_ab_op : or_op abstr_bool := 
  λ ab1 ab2,
    match ab1, ab2 with
    | Top, _ | _, Top => Top
    | NotTop b1, NotTop b2 => NotTop (orb b1 b2)
    end. 

Instance or_ab_sound : or_op_sound abstr_bool bool.
Proof.
  intros ab1 ab2 b1 b2 H1 H2. destruct ab1, ab2, b1, b2; auto; gamma_destruct;
  constructor; auto.
Qed.
Hint Resolve or_ab_sound : soundness.

(** ** Negation *)
Instance neg_ab_op : neg_op abstr_bool := 
  λ ab,
    match ab with
    | Top => Top
    | NotTop b => NotTop (negb b)
    end.

Instance neg_ab_sound : neg_op_sound neg_ab_op neg_op_bool.
Proof.
  intros ab b H; destruct ab, b; inversion H; subst; eauto with soundness.
Qed.
Hint Resolve neg_ab_sound : soundness.

(** ** If *)
Instance if_ab_op {B} {JB : Joinable B B} : if_op abstr_bool B := 
  λ ab : abstr_bool,
    λ p1 : B, λ p2 : B,
    match ab with
    | Top => p1 ⊔ p2
    | NotTop b => if b then p1 else p2
    end.

Instance if_ab_op_sound {B B' : Type} {JB : Joinable B B} {GB : Galois B B'} : 
  JoinableSound JB →
  if_op_sound if_ab_op if_op_bool.
Proof.
  intros JBS ab b p1 p2 p1' p2' Hb Hp1 Hp2; destruct ab, b; inversion Hb;
  try discriminate; try assumption; simpl. 
  - apply join_sound; left; apply Hp1.
  - apply join_sound; right; apply Hp2.
Qed.
Hint Resolve if_ab_op_sound : soundness.

Definition ab_le (a b : abstr_bool) : Prop := a = b.
Hint Unfold ab_le : preorders.

Instance preorder_ab : PreorderedSet abstr_bool.
Proof. proof_preorder ab_le. Defined.

Instance abstr_bool_joinable : Joinable abstr_bool abstr_bool :=
  λ ab1, λ ab2, 
    match ab1, ab2 with
    | NotTop true, NotTop true => NotTop true
    | NotTop false, NotTop false => NotTop false
    | _, _ => Top
    end.

Instance abstr_bool_joinable_idem : 
  JoinableIdem abstr_bool_joinable.
Proof.
  intro b; destruct b. 
  - constructor. 
  - destruct b; reflexivity.
Qed.

Instance preorder_boolean_sound : PreorderSound abstr_bool bool.
Proof.
  intros x y Hpre n Hgamma. destruct x, y; subst; inversion Hpre; 
    eauto with soundness. 
Qed.

Instance join_boolean_sound : JoinableSound abstr_bool_joinable.
Proof.
  intros x y; destruct x, y; cbv.
  - reflexivity.
  - reflexivity.
  - intros b' H.
    destruct b; reflexivity.
  - intros b' [H | H]; subst. 
    + destruct b', b0; reflexivity.
    + destruct b, b'; reflexivity.
Qed.

