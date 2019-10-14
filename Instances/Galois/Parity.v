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

Lemma even_extract_pareven : forall n,
  even n -> extract_par n = par_even.
Proof. 
  intros. 
  apply even_equiv in H. destruct H as [k H]; subst.
  induction k.
  - (*  0 *)
    reflexivity.
  - (* S x *)
    replace (2 * S k) with (S (S (2 * k))).
    + repeat rewrite extract_S_n. rewrite IHk. reflexivity.
    + ring.
Qed.

Lemma odd_extract_parodd : forall n, odd n -> extract_par n = par_odd.
Proof. 
  intros. apply odd_equiv in H. destruct H as [k H]; subst.
  induction k.
  - reflexivity.
  - replace (2 * (S k) + 1) with (S(2 * (S k))).
    rewrite extract_S_n. replace (2 * S k) with  (S ((2 * k + 1))).
    rewrite extract_S_n. rewrite IHk. reflexivity. ring. ring.
Qed.

Lemma gamma_par_extract_n_n : forall n,
  gamma_par (extract_par n) n.
Proof.
  intros. pose proof even_or_odd as Hpar. 
  destruct Hpar with (n:=n) as [Heven | Hodd].
  - pose proof Heven.
    apply even_extract_pareven in Heven. rewrite Heven.
    apply H.
  - pose proof Hodd. apply odd_extract_parodd in Hodd.
    rewrite Hodd. apply H.
Qed.
