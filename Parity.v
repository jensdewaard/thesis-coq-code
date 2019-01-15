Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import Aux.

Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity
  | par_top : parity
  | par_bottom : parity.

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

