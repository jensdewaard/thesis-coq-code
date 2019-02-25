Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.
Require Import Coq.Sets.Partial_Order.

Require Import AbstractBool.
Require Import Aux.
Require Import Preorder.

(** * Parity *)

Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity
  | par_top : parity
  | par_bottom : parity.

Inductive parity_ensemble : parity -> Prop :=
  | par_ens_all : forall p, parity_ensemble p.

Inductive parity_le : parity -> parity -> Prop :=
  | lt_top : forall p, parity_le p par_top
  | lt_bottom : forall p, parity_le par_bottom p
  | lt_refl : forall p, parity_le p p.

Lemma parity_le_refl : forall p, parity_le p p.
destruct p; constructor. Qed.

Lemma parity_le_trans : forall p1 p2 p3,
  parity_le p1 p2 -> parity_le p2 p3 -> parity_le p1 p3.
destruct p1, p2, p3; intros; try constructor; 
  try inversion H; try inversion H0. Qed.

Instance proset_parity : PreorderedSet parity :=
{
  preorder := parity_le;
  preorder_refl := parity_le_refl;
  preorder_trans := parity_le_trans;
}.

(** ** Abstraction and concretizations functions *)

Definition gamma_par (p : parity) : nat -> Prop :=
  match p with
  | par_even => even 
  | par_odd => odd 
  | par_top => (fun n => True)
  | par_bottom => fun n => False
  end.

Fixpoint extract_par (n : nat) : parity :=
  match n with 
  | 0 => par_even
  | S 0 => par_odd
  | S (S n) => extract_par n
  end.

Definition sound_par (p : parity) (n : nat) := gamma_par p n.

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


Lemma extract_S_n : forall n,
  extract_par (S n) = parity_plus (extract_par n) par_odd.
Proof.
  intros. induction n.
  - reflexivity.
  - rewrite -> IHn. simpl. rewrite -> parity_plus_assoc. simpl.
    rewrite <- parity_plus_par_even. reflexivity.
Qed.

Lemma extract_distr : forall n m,
  extract_par (n + m) = parity_plus (extract_par n) (extract_par m).
Proof.
  intros n m. generalize dependent n. induction m.
  - intros. simpl. rewrite <- parity_plus_par_even.
    rewrite <- plus_n_O. reflexivity.
  - intros. rewrite -> extract_S_n. 
    replace (extract_par (n + S m)) with (extract_par (S(n+m))).
    rewrite -> extract_S_n, IHm, parity_plus_assoc. 
    reflexivity.
    rewrite -> plus_comm. rewrite <- Nat.add_succ_l. rewrite -> plus_comm. 
    reflexivity.
Qed.

Corollary extract_par_even_odd_alternate : forall n,
  extract_par n = par_even -> extract_par (S n) = par_odd.
Proof.
  intros. rewrite extract_S_n. rewrite H.
  reflexivity.
Qed.

Corollary extract_par_odd_even_alternate : forall n,
  extract_par n = par_odd -> extract_par (S n) =  par_even.
Proof.
  intros. rewrite extract_S_n. rewrite H. reflexivity.
Qed.

Lemma even_extract_pareven : forall n,
  even n -> extract_par n = par_even.
Proof. 
  intros. apply even_equiv in H. destruct H. subst.
  induction x.
  - (*  0 *)
    reflexivity.
  - (* S x *)
    replace (mult 2 (S x)) with (plus (mult 2 x) 2).
    + rewrite extract_distr. rewrite IHx. reflexivity.
    + simpl. rewrite <- plus_n_O. 
      rewrite -> add_succ_r. rewrite -> add_succ_r. rewrite <- plus_n_O.
      rewrite <- add_succ_r. reflexivity.
Qed.

Corollary odd_extract_parodd : forall n,
  odd n -> extract_par n = par_odd.
Proof. 
  intros. induction n.
  - inversion H.
  - inversion H; subst. apply extract_par_even_odd_alternate. 
    apply even_extract_pareven. assumption.
Qed.

Lemma extract_pareven_even : forall n,
  extract_par n = par_even -> even n.
Proof. 
  intros. assert (even n \/ odd n).
  { apply even_or_odd. }
  destruct H0. assumption.
  inversion H0; subst. 
  apply odd_extract_parodd in H0. rewrite H0 in H. inversion H.
Qed.

Corollary extract_parodd_odd : forall n,
  extract_par n = par_odd -> odd n.
Proof. 
  intros. 
  pose proof even_or_odd as Hor.
  destruct Hor with (n:=n).
  - apply even_extract_pareven in H0. rewrite H0 in H. inversion H.
  - assumption.
Qed.

Lemma never_extract_parbottom : ~ exists n,
  extract_par n = par_bottom.
Proof. 
  unfold not; intros; destruct H.
  pose proof even_or_odd as Hpar.
  destruct Hpar with (n:=x).
  - apply even_extract_pareven in H0. rewrite H0 in H. inversion H.
  - apply odd_extract_parodd in H0. rewrite H0 in H. inversion H.
Qed.

Lemma gamma_par_S_S_n : forall n p,
  gamma_par p n -> gamma_par p (S (S n)).
Proof.
  destruct p; simpl; intros.
  - repeat constructor. assumption.
  - repeat constructor; assumption.
  - constructor.
  - inversion H.
Qed.

Lemma gamma_par_extract_par_n_p : forall n p,
  gamma_par p n -> extract_par n = p \/ p = par_top.
Proof. 
  intros. induction n.
  - destruct p; try reflexivity; try inversion H.
    + left. reflexivity.
    + right. reflexivity.
  - destruct p; try reflexivity; try inversion H.
    + subst. left. apply odd_extract_parodd in H1. 
      apply extract_par_odd_even_alternate in H1. assumption.
    + subst. left. apply even_extract_pareven in H1.
      apply extract_par_even_odd_alternate in H1. assumption.
    + right. reflexivity.
Qed.

Lemma gamma_extract_n_n : forall n,
  gamma_par (extract_par n) n.
Proof.
  intros. destruct (extract_par n) eqn:H.
  - induction n.
    + simpl. constructor.
    + simpl. apply extract_pareven_even in H. assumption.
  - induction n.
    + simpl. inversion H.
    + simpl. apply extract_parodd_odd in H. assumption.
  - simpl. constructor.
  - pose proof never_extract_parbottom as H1.
    unfold not in H1. exfalso. apply H1. exists n. assumption.
Qed.

Lemma gamma_par_add_even : forall p n1 n2,
  gamma_par p n1 ->
  even n2 ->
  gamma_par p (n1 + n2).
Proof.
  intros. destruct p.
  - simpl in *. apply even_even_plus; assumption.
  - simpl in *. apply odd_plus_l; assumption.
  - simpl in *. constructor.
  - inversion H.
Qed.

Lemma parity_plus_sound : forall p1 p2 n1 n2,
  sound_par p1 n1 ->
  sound_par p2 n2 ->
  sound_par (parity_plus p1 p2) (n1 + n2).
Proof.
  destruct p1, p2; simpl; try tauto;
    eauto using odd_even_plus, even_even_plus, odd_plus_l, odd_plus_r.
Qed.

Lemma parity_mult_sound: forall p1 p2 n1 n2,
  sound_par p1 n1 ->
  sound_par p2 n2 ->
  sound_par (parity_mult p1 p2) (n1 * n2).
Proof.
  destruct p1, p2; simpl; try tauto;
    eauto using even_mult_l, even_mult_r, odd_mult.
Qed.

(** Equality *)
Definition parity_eq (p1 p2 : parity) : abstr_bool :=
  match p1, p2 with
  | par_even, par_odd => ab_false
  | par_odd, par_even => ab_false
  | par_bottom, _ | _, par_bottom => ab_bottom
  | _, _ => ab_top
  end.

Lemma Is_true_eqb n1 n2 : Bool.Is_true (Nat.eqb n1 n2) <-> n1 = n2.
Admitted.

Lemma parity_eq_sound : forall p1 p2 n1 n2,
  gamma_par p1 n1 ->
  gamma_par p2 n2 -> 
  gamma_bool (parity_eq p1 p2) (Nat.eqb n1 n2).
Proof.
  destruct p1, p2; simpl; try tauto.
  - intros n1 n2 ?? ->%Is_true_eqb. eauto using not_even_and_odd.
  - intros n1 n2 ?? ->%Is_true_eqb. eauto using not_even_and_odd.
Qed.

(** ** Join *)
Definition parity_join (p1 p2 : parity) : parity :=
  match p1, p2 with
  | par_bottom, p | p, par_bottom => p
  | par_top, _ | _, par_top => par_top
  | par_even, par_even => par_even
  | par_odd, par_odd => par_odd
  | par_even, par_odd | par_odd, par_even => par_top 
  end.

Lemma parity_join_comm : forall (p1 p2 : parity),
  parity_join p1 p2 = parity_join p2 p1.
Proof. destruct p1, p2; auto. Qed.

Lemma parity_join_assoc : forall (p1 p2 p3 : parity),
  parity_join p1 (parity_join p2 p3) = parity_join (parity_join p1 p2) p3.
Proof. 
  intros. destruct p1, p2, p3; auto.
Qed.

Lemma parity_join_idem : forall (p : parity),
  parity_join p p = p.
Proof. 
  intros. destruct p; auto.
Qed.
  
Lemma parity_join_sound_left : forall p1 p2 n,
  gamma_par p1 n -> gamma_par (parity_join p1 p2) n.
Proof. 
  intros. destruct p1, p2; simpl in *; tauto. 
Qed.

Corollary parity_join_sound_right : forall p1 p2 n,
  gamma_par p2 n -> gamma_par (parity_join p1 p2) n.
Proof. 
  intros. destruct p1, p2; simpl in *; tauto. 
Qed.

(** ** Meet *)
Definition parity_meet (p1 p2 : parity) : parity :=
  match p1, p2 with
  | par_bottom, _ | _, par_bottom => par_bottom
  | par_top, p | p, par_top => p
  | par_even, par_even => par_even
  | par_odd, par_odd => par_odd
  | par_even, par_odd | par_odd, par_even => par_bottom
  end.

Lemma parity_meet_comm : forall (p1 p2 : parity),
  parity_meet p1 p2 = parity_meet p2 p1.
Proof. 
  intros. destruct p1, p2; auto. 
Qed.

Lemma parity_meet_assoc : forall (p1 p2 p3 : parity),
  parity_meet p1 (parity_meet p2 p3) = parity_meet (parity_meet p1 p2) p3.
Proof. 
  intros. destruct p1, p2, p3; auto.
Qed.

Lemma parity_meet_idem : forall (p : parity),
  parity_meet p p = p.
Proof. 
  intros. destruct p; auto. 
Qed.

