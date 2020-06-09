Require Export Base.
Require Import Coq.Arith.Arith Coq.Arith.PeanoNat Coq.Arith.Even
  Coq.Sets.Partial_Order Types.AbstractBool Classes.PreorderedSet
  Classes.Joinable Classes.Galois Classes.IsNat Psatz.

(* We start with some lemmas about Nat.Even and Nat.Odd that are missing from
   the standard library in their current, not-deprecated form. *)

Lemma Nat_even_mul_l : ∀ n m,
  Nat.Even n → Nat.Even (Nat.mul n m).
Proof.
  intros n m Hn. 
  destruct Hn; subst; rewrite <- Nat.mul_assoc.
  exists (x * m). reflexivity.
Qed.

Corollary Nat_even_mul_r : ∀ n m,
  Nat.Even m → Nat.Even (Nat.mul n m).
Proof.
  intros n m Hm.  rewrite Nat.mul_comm. apply Nat_even_mul_l.
  assumption.
Qed.
Hint Resolve Nat_even_mul_l Nat_even_mul_r : arith.

Lemma Nat_mult_odd : ∀ n m,
  Nat.Odd n →
  Nat.Odd m →
  Nat.Odd (n * m).
Proof.
  intros n m Hn Hm. 
  rewrite <- odd_equiv in Hn, Hm; rewrite <- odd_equiv.
  apply odd_mult; assumption.
Qed.
Hint Resolve Nat_mult_odd : arith.

(** * Parity *)

Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity
  | par_top : parity.
Instance parity_top : top_op parity := par_top.

Inductive gamma_par : parity → ℘ nat :=
  | gamma_par_even : ∀ n, Nat.Even n → gamma_par par_even n
  | gamma_par_odd  : ∀ n, Nat.Odd n → gamma_par par_odd n
  | gamma_par_top : ∀ n, gamma_par par_top n.

Instance galois_parity_nat : Galois parity nat := gamma_par.

(** ** Operations *)
Instance extract_parity : extract_op nat parity := λ n,
  if Nat.even n then par_even else par_odd.

Instance extract_parity_sound : extract_op_sound extract_parity extract_nat.
Proof.
  intro n. unfold extract, extract_parity, extract_nat. rewrite id_refl.
  destruct (Nat.even n) eqn:H. constructor. rewrite Nat.even_spec in H.
  assumption. rewrite <- Bool.negb_true_iff in H. 
  rewrite Nat.negb_even in H. rewrite Nat.odd_spec in H. constructor.
  assumption.
Qed.
Hint Resolve extract_parity_sound : soundness.

(** *** Plus *)
Definition parity_plus (p q : parity) : parity :=
  match p with 
  | par_even => q
  | par_odd => match q with
               | par_even => par_odd
               | par_odd => par_even
               | par_top => par_top
               end
  | par_top => par_top
  end.
Instance parity_plus_op : plus_op parity parity  := parity_plus.

Instance parity_plus_sound : plus_op_sound parity_plus_op nat_plus_op.
Proof.
  intros p q n m Hpn Hqm. destruct p, q; try constructor.
  - cbn. inversion Hpn; subst. inversion Hqm; subst.
    unfold plus. unfold nat_plus_op. destruct H.
    destruct H0. subst. rewrite <- Nat.mul_add_distr_l.
    econstructor. reflexivity.
  - cbn. inversion Hpn; subst. inversion Hqm; subst. destruct H, H0; subst.
    unfold plus; unfold nat_plus_op.  rewrite plus_assoc.
    rewrite <- Nat.mul_add_distr_l. econstructor. reflexivity. 
  - cbn. unfold plus, nat_plus_op. inversion Hqm; subst. 
    inversion Hpn; subst. destruct H, H0; subst. rewrite plus_comm. rewrite
    plus_assoc. rewrite <- Nat.mul_add_distr_l. econstructor. reflexivity.
  - unfold plus, nat_plus_op. inversion Hpn; inversion Hqm;
    subst. destruct H, H0; subst. rewrite plus_assoc. 
    replace (Nat.add (Nat.add (Nat.add (Nat.mul 2 x) 1) (Nat.mul 2 x0)) 1) with
      (S ( S( (Nat.add (Nat.mul 2 x) (Nat.mul 2 x0))))).
    rewrite <- Nat.mul_add_distr_l. rewrite Nat.Even_succ_succ.
    econstructor. reflexivity. lia.
Qed.
Hint Resolve parity_plus_sound : soundness.

Definition parity_mult (p q : parity) : parity :=
  match p, q with
  | par_even, _ | _, par_even => par_even
  | par_top,  _ | _, par_top => par_top
  | _, _ => par_odd
  end.
Instance parity_mult_op : mult_op parity parity := parity_mult.

Instance parity_mult_sound : mult_op_sound parity_mult_op nat_mult_op.
Proof.
  intros p q n m Hpn Hqm. destruct p, q; cbn; constructor;
    inversion Hpn; inversion Hqm; subst; clear Hpn; clear Hqm; unfold mult,
    mult_op, nat_mult_op; auto with arith.
Qed.
Hint Resolve parity_mult_sound : soundness.

(** Equality *)
Definition parity_eq (p1 p2 : parity) : abstr_bool :=
  match p1, p2 with
  | par_even, par_odd => NotTop false
  | par_odd, par_even => NotTop false
  | _, _ => Top
  end.
Instance parity_eq_op : eq_op parity abstr_bool := parity_eq.

Instance parity_eq_sound : eq_op_sound (B:=abstr_bool) parity_eq_op nat_eq_op.
Proof.
  intros p q n m Hpn Hqm. 
  destruct p, q; try constructor; gamma_destruct;
    unfold γ; simpl; symmetry;
    unfold eq, nat_eq_op; rewrite Nat.eqb_neq; intro Hnot; subst;
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
  | par_le_odd  : parity_le par_odd par_odd 
  | par_le_top : ∀ p, parity_le p par_top.
Hint Constructors parity_le : preorders.

Global Instance proset_parity : PreorderedSet parity.
Proof. proof_preorder parity_le. Defined.

Instance parity_joinable : Joinable parity parity :=
  λ p1, λ p2, 
    match p1, p2 with
    | par_even, par_even => par_even
    | par_odd, par_odd => par_odd
    | _, _ => top
    end.

Instance parity_joinable_idem : 
  JoinableIdem parity_joinable.
Proof.
  intro a; destruct a; constructor.
Qed.
      
Instance join_parity_nat_sound : JoinableSound parity_joinable.
Proof.
  intros x y z H. destruct x, y; cbv in *; constructor;
  destruct H; inversion H; subst; assumption.
Qed.

Instance preorder_parity_sound : PreorderSound parity nat.
Proof.
  intros x y Hpre n Hgamma. 
  destruct x, y; inversion Hpre; eauto with soundness; constructor.
Qed.


