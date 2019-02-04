Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.
Require Import Coq.Sets.Partial_Order.

Require Import Aux.

Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity
  | par_top : parity
  | par_bottom : parity.

Inductive parity_ensemble : parity -> Prop :=
  | par_ens_all : forall p, parity_ensemble p.

Inductive parity_lt : parity -> parity -> Prop :=
  | lt_top : forall p, parity_lt p par_top
  | lt_bottom : forall p, parity_lt par_bottom p.

Definition parity_PO := Definition_of_PO parity parity_ensemble parity_lt.


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

Fixpoint extract (n : nat) : parity :=
  match n with 
  | 0 => par_even
  | S 0 => par_odd
  | S (S n) => extract n
  end.

Lemma extract_S_n : forall n,
  extract (S n) = parity_plus (extract n) par_odd.
Proof.
  intros. induction n.
  - reflexivity.
  - rewrite -> IHn. simpl. rewrite -> parity_plus_assoc. simpl.
    rewrite <- parity_plus_par_even. reflexivity.
Qed.

Lemma extract_distr : forall n m,
  extract (n + m) = parity_plus (extract n) (extract m).
Proof.
  intros n m. generalize dependent n. induction m.
  - intros. simpl. rewrite <- parity_plus_par_even.
    rewrite <- plus_n_O. reflexivity.
  - intros. rewrite -> extract_S_n. 
    replace (extract (n + S m)) with (extract (S(n+m))).
    rewrite -> extract_S_n, IHm, parity_plus_assoc. 
    reflexivity.
    rewrite -> plus_comm. rewrite <- Nat.add_succ_l. rewrite -> plus_comm. 
    reflexivity.
Qed.

Corollary extract_par_even_odd_alternate : forall n,
  extract n = par_even -> extract (S n) = par_odd.
Proof.
  intros. rewrite extract_S_n. rewrite H.
  reflexivity.
Qed.

Corollary extract_par_odd_even_alternate : forall n,
  extract n = par_odd -> extract (S n) =  par_even.
Proof.
  intros. rewrite extract_S_n. rewrite H. reflexivity.
Qed.

Lemma even_extract_pareven : forall n,
  even n -> extract n = par_even.
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
  odd n -> extract n = par_odd.
Proof. 
  intros. induction n.
  - inversion H.
  - inversion H; subst. apply extract_par_even_odd_alternate. 
    apply even_extract_pareven. assumption.
Qed.

Lemma extract_pareven_even : forall n,
  extract n = par_even -> even n.
Proof. 
  intros. assert (even n \/ odd n).
  { apply even_or_odd. }
  destruct H0. assumption.
  inversion H0; subst. 
  apply odd_extract_parodd in H0. rewrite H0 in H. inversion H.
Qed.

Corollary extract_parodd_odd : forall n,
  extract n = par_odd -> odd n.
Proof. 
  intros. 
  pose proof even_or_odd as Hor.
  destruct Hor with (n:=n).
  - apply even_extract_pareven in H0. rewrite H0 in H. inversion H.
  - assumption.
Qed.

Lemma never_extract_parbottom : ~ exists n,
  extract n = par_bottom.
Proof. 
  unfold not; intros; destruct H.
  pose proof even_or_odd as Hpar.
  destruct Hpar with (n:=x).
  - apply even_extract_pareven in H0. rewrite H0 in H. inversion H.
  - apply odd_extract_parodd in H0. rewrite H0 in H. inversion H.
Qed.

(* Concretization function gamma for parity *)

Definition gamma (p : parity) : (nat -> Prop) :=
  match p with
  | par_even => even
  | par_odd => odd
  | par_top => isNumber
  | par_bottom => noNumber
  end.

Lemma gamma_S_S_n : forall n p,
  gamma p n -> gamma p (S (S n)).
Proof.
  destruct p; simpl; intros.
  - repeat constructor. assumption.
  - repeat constructor; assumption.
  - constructor.
  - inversion H.
Qed.

Lemma gamma_extract_n_p : forall n p,
  gamma p n -> extract n = p \/ p = par_top.
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
  gamma (extract n) n.
Proof.
  intros. destruct (extract n) eqn:H.
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

Lemma gamma_add_even : forall p n1 n2,
  gamma p n1 ->
  even n2 ->
  gamma p (n1 + n2).
Proof.
  intros. destruct p.
  - simpl in *. apply even_even_plus; assumption.
  - simpl in *. apply odd_plus_l; assumption.
  - simpl in *. constructor.
  - inversion H.
Qed.

Lemma gamma_distr_plus: forall p1 p2 n1 n2,
  gamma p1 n1 ->
  gamma p2 n2 ->
  gamma (parity_plus p1 p2) (n1 + n2).
Proof.
  intros. destruct p2.
  - (* p2 = par_even *)
    rewrite <- parity_plus_par_even. apply gamma_add_even.
    simpl in H0. assumption. assumption.
  - (* p2 = par_odd *)
    simpl in *. Search gamma. destruct p1.
    + simpl. apply odd_plus_r. simpl in H. assumption. assumption.
    + Search even. simpl in *. apply odd_even_plus; assumption. 
    + simpl. constructor.
    + inversion H.
  - (* p2 = par_top *)
    simpl. rewrite <- parity_plus_comm. destruct p1; simpl; try constructor.
    inversion H.
  - inversion H0.
Qed.

Lemma gamma_distr_mult: forall p1 p2 n1 n2,
  gamma p1 n1 ->
  gamma p2 n2 ->
  gamma (parity_mult p1 p2) (n1 * n2).
Proof.
  intros. destruct p1; simpl in *.
  - (* p1 = par_even *)
    apply even_mult_l. assumption.
  - (* p1 = par_odd *)
    destruct p2; simpl in *.
    + (* p2 = par_even *)
      apply even_mult_r. assumption.
    + (* p2 = par_odd *)
      apply odd_mult; assumption.
    + (* p2 = par_top *)
      constructor.
    + (* p2 = par_bottom *)
      inversion H0.
  - (* p1 = par_top *)
    constructor.
  - inversion H.
Qed.

