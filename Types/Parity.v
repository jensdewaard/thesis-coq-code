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

Instance parity_plus_sound : plus_op_sound parity_plus_op nat_plus_op.
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
Hint Resolve parity_plus_sound : soundness.

Definition parity_mult (p q : parity) : parity :=
  match p with
  | par_even => par_even
  | par_odd => q
  end.
Instance parity_mult_op : mult_op parity parity := parity_mult.

Instance parity_mult_sound : mult_op_sound parity_mult_op nat_mult_op.
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
Hint Resolve parity_mult_sound : soundness.

(** Equality *)
Definition parity_eq (p1 p2 : parity) : (abstr_bool+⊤) :=
  match p1, p2 with
  | par_even, par_odd => NotTop ab_false
  | par_odd, par_even => NotTop ab_false
  | _, _ => Top
  end.
Instance parity_eq_op : eq_op parity (abstr_bool+⊤) := parity_eq.

Instance parity_eq_sound : eq_op_sound (B:=abstr_bool+⊤) parity_eq_op nat_eq_op.
Proof.
  intros p q n m Hpn Hqm. destruct p, q; constructor; gamma_destruct; unfold
  eq, nat_eq_op; rewrite Nat.eqb_neq; unfold not; intro Hnot; subst;
  apply (Nat.Even_Odd_False m); assumption.
Qed.
Hint Resolve parity_eq_sound : soundness.

Instance parity_leb_op : leb_op parity (abstr_bool+⊤) := λ _, λ _, Top.
Instance parity_leb_sound : 
  leb_op_sound (B:=abstr_bool+⊤) parity_leb_op nat_leb_op.
Proof.
  intros p q n m Hpn Hqm. unfold leb, parity_leb_op, nat_leb_op.
  constructor.
Qed.
Hint Resolve parity_leb_sound : soundness.

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


