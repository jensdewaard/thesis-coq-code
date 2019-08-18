Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.

Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.Parity.
Require Import Instances.IsNat.Parity.
Require Import Types.Parity.

Definition gamma_par (p : parity) : nat -> Prop :=
  match p with
  | par_even => even 
  | par_odd => odd 
  | par_top => (fun n => True)
  | par_bottom => fun n => False
  end.

Lemma gamma_par_monotone : forall p1 p2,
  preorder p1 p2 -> preorder (gamma_par p1) (gamma_par p2).
Proof.
  destruct p1, p2; simpl; intros; try constructor; try inversion H;
  intros; try tauto.
Qed.

Instance galois_parity_nat : Galois nat parity :=
{
  gamma := gamma_par;
  gamma_monotone := gamma_par_monotone;
}.


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
    rewrite -> extract_S_n, IHm, parity_plus_assoc. reflexivity.
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
    + simpl. rewrite <- plus_n_O. rewrite plus_comm. simpl.
      rewrite <- Nat.add_succ_l. rewrite plus_comm.
      reflexivity.
Qed.


Corollary odd_extract_parodd : forall n, odd n -> extract_par n = par_odd.
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
  intros. pose proof even_or_odd as Hor.
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

Lemma gamma_par_extract_n_n : forall n,
  gamma_par (extract_par n) n.
Proof.
  intros. destruct (extract_par n) eqn:H.
  - induction n.
    + simpl. constructor.
    + simpl. apply extract_pareven_even in H. assumption.
  - induction n.
    + simpl. inversion H.
    + simpl. apply extract_parodd_odd in H.
      assumption.
  - simpl. constructor.
  - pose proof never_extract_parbottom as H1.
    unfold not in H1. exfalso.
    apply H1. exists n. assumption.
Qed.

