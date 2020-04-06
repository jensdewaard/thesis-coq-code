Require Export Base.
Require Import Coq.Arith.Arith Coq.Arith.PeanoNat Coq.Arith.Even
  Coq.Sets.Partial_Order Types.AbstractBool Classes.PreorderedSet
  Classes.Joinable Classes.Galois Classes.IsNat Psatz.

(** * Parity *)

Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity.

Inductive gamma_par : parity → ℘ nat :=
  | gamma_par_even : ∀ n, Nat.Even n → gamma_par par_even n
  | gamma_par_odd  : ∀ n, Nat.Odd n → gamma_par par_odd n.
Hint Constructors gamma_par : soundness.

Instance galois_parity_nat : Galois parity nat := gamma_par.

(** ** Operations *)

(** *** Plus *)
Definition parity_plus (p q : parity) : parity :=
  match p with 
  | par_even => q
  | par_odd => match q with
               | par_even => par_odd
               | par_odd => par_even
               end
  end.
Instance parity_plus_op : plus_op parity parity  := parity_plus.

Instance parity_plus_sound : plus_op_sound parity nat.
Proof.
  intros p q n m Hpn Hqm. destruct p, q. 
  - cbn. inversion Hpn; subst. constructor. inversion Hqm; subst.
    unfold plus. unfold nat_plus_op. destruct H.
    destruct H0. subst. rewrite <- Nat.mul_add_distr_l.
    econstructor. reflexivity.
  - cbn. inversion Hpn; subst. inversion Hqm; subst. destruct H, H0; subst.
    constructor. unfold plus; unfold nat_plus_op.  rewrite plus_assoc.
    rewrite <- Nat.mul_add_distr_l. econstructor. reflexivity. 
  - cbn. unfold plus, nat_plus_op. constructor. inversion Hqm; subst. 
    inversion Hpn; subst. destruct H, H0; subst. rewrite plus_comm. rewrite
    plus_assoc. rewrite <- Nat.mul_add_distr_l. econstructor. reflexivity.
  - cbn. constructor. unfold plus, nat_plus_op. inversion Hpn; inversion Hqm;
    subst. destruct H, H0; subst. rewrite plus_assoc. 
    replace (Nat.add (Nat.add (Nat.add (Nat.mul 2 x) 1) (Nat.mul 2 x0)) 1) with
      (S ( S( (Nat.add (Nat.mul 2 x) (Nat.mul 2 x0))))).
    rewrite <- Nat.mul_add_distr_l. rewrite Nat.Even_succ_succ.
    econstructor. reflexivity. lia.
Qed.

Definition parity_mult (p q : parity) : parity :=
  match p with
  | par_even => par_even
  | par_odd => q
  end.
Instance parity_mult_op : mult_op parity parity := parity_mult.

Instance parity_mult_sound : mult_op_sound parity nat.
Proof.
  intros p q n m Hpn Hqm. destruct p, q; cbn; constructor; inversion Hpn;
  inversion Hqm; destruct H, H0; clear Hpn; clear Hqm; subst; unfold mult,
  nat_mult_op.
  - rewrite <- mult_assoc. econstructor; reflexivity.
  - rewrite <- mult_assoc. econstructor; reflexivity.
  - rewrite mult_assoc. rewrite (mult_comm (Nat.add (Nat.mul 2 x) 1) 2).
    rewrite <- mult_assoc. econstructor; reflexivity.
  - rewrite <- odd_equiv. apply odd_mult; rewrite odd_equiv; econstructor;
    reflexivity.
Qed.

(** Equality *)
Definition parity_eq (p1 p2 : parity) : (abstr_bool+⊤) :=
  match p1, p2 with
  | par_even, par_odd => NotTop ab_false
  | par_odd, par_even => NotTop ab_false
  | _, _ => Top
  end.
Instance parity_eq_op : eq_op parity (abstr_bool+⊤) := parity_eq.

Instance parity_eq_sound : eq_op_sound (B:=abstr_bool+⊤) parity nat.
Proof.
  intros p q n m Hpn Hqm. destruct p, q; constructor; gamma_destruct; unfold
  eq, nat_eq_op; rewrite Nat.eqb_neq; unfold not; intro Hnot; subst;
  apply (Nat.Even_Odd_False m); assumption.
Qed.

Instance parity_leb_op : leb_op parity (abstr_bool+⊤) := λ _, λ _, Top.
Instance parity_leb_sound : leb_op_sound (B:=abstr_bool+⊤) parity nat.
Proof.
  intros p q n m Hpn Hqm. unfold leb, parity_leb_op, nat_leb_op.
  constructor.
Qed.

(* Some lemmas regarding Nat.Even and Nat.Odd that are missing but are included
 * for the deprecated even and odd. We define these lemmas here so we can use the  
 * newer definitions for when the older version are deleted. *)
(*Lemma Even_add : forall n m, Nat.Even n -> Nat.Even m -> Nat.Even (n + m).
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
*)
Inductive parity_le : parity → parity → Prop :=
  | par_le_even : parity_le par_even par_even
  | par_le_odd  : parity_le par_odd par_odd. 
Hint Constructors parity_le : preorders.

Global Instance proset_parity : PreorderedSet parity.
Proof. proof_preorder parity_le. Defined.

Instance parity_joinable : Joinable parity (parity+⊤) :=
  λ p1, λ p2, 
    match p1, p2 with
    | par_even, par_even => NotTop par_even
    | par_odd, par_odd => NotTop par_odd
    | _, _ => Top
    end.
      
Instance join_parity_nat_sound : JoinableSound parity (parity+⊤) nat.
Proof.
  intros x y z H. destruct x, y; cbv in *; constructor.
  - destruct H; inversion H; subst; assumption.
  - destruct H; inversion H; subst; assumption.
Qed.

Instance preorder_parity_sound : PreorderSound parity nat.
Proof.
  intros x y Hpre n Hgamma. destruct x, y; eauto with soundness; inversion
  Hpre.
Qed.


