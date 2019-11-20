Require Export Base.
Require Import Classes.Applicative.
Require Import Classes.IsNat.
Require Import Classes.Monad.
Require Import Coq.Arith.Arith.
Require Import Instances.Monad.
Require Import Instances.Monad.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Parity.
Require Import Types.State.

Definition ensure_par (v : avalue) : AbstractState parity :=
  match v with
  | VParity x => liftT (pure x)
  | _ => liftT (pure NoneA)
  end.

Definition extract_par (n : nat) : parity :=
  if Nat.even n then par_even else par_odd.
Hint Unfold extract_par : soundness.

Lemma extract_S_n : forall n,
  extract_par (S n) = parity_plus (extract_par n) par_odd.
Proof. 
  simple_solve. 
  - destruct n. discriminate. rewrite Nat.even_spec in Heqb.
    rewrite Nat.even_succ in Heqb0. rewrite Nat.odd_spec in Heqb0.
    exfalso. apply Nat.Even_Odd_False with (x:=n);
    assumption. 
  - destruct n. simpl in Heqb0. discriminate. rewrite Nat.even_succ in Heqb0.
    assert ((Nat.even n || Nat.odd n)%bool = true).
    apply Nat.orb_even_odd. rewrite Heqb in H. rewrite Heqb0 in H.
    simpl in H. discriminate.
Qed.

Lemma even_extract_pareven_equiv : forall n,
  Nat.Even n <-> extract_par n = par_even.
Proof. 
  intros. split; intro H. 
  - unfold extract_par. destruct (Nat.even n) eqn:H'. reflexivity.
    rewrite <- Nat.even_spec in H. rewrite H in H'. discriminate.
  - unfold extract_par in H. destruct (Nat.even n) eqn:H'.
    rewrite Nat.even_spec in H'. assumption. discriminate.
Qed.

Lemma odd_extract_parodd_equiv : forall n, 
  Nat.Odd n <-> extract_par n = par_odd.
Proof. 
  split; intro H.
  - unfold extract_par. unmatch (Nat.even n).
    + rewrite Nat.even_spec in Heqb. exfalso. apply Nat.Even_Odd_False with
      (x:=n); assumption.
    + reflexivity.
  - unfold extract_par in H. unmatch (Nat.even n). discriminate.
    apply Nat.odd_spec. unfold Nat.odd. rewrite Heqb. auto.
Qed.
Hint Rewrite <- even_extract_pareven_equiv odd_extract_parodd_equiv :
  soundness.

Definition extract_parM (n : nat) : AbstractState parity :=
  liftT (pure (extract_par n)).

Definition pplusM (n m : parity) : AbstractState parity :=
  liftT (pure (parity_plus n m)).

Definition pmultM (n m : parity) : AbstractState parity :=
  liftT (pure (parity_mult n m )).

Definition peqM (n m : parity) : AbstractState abstr_bool :=
  liftT (pure (parity_eq n m)).

Definition pleM (n m : parity) : AbstractState abstr_bool :=
  liftT (pure ab_top).

Definition build_parity (p : parity) : AbstractState avalue :=
  liftT (pure (VParity p)).

Global Instance isnat_parity : 
  IsNat AbstractState avalue abstr_bool parity :=
{
  ensure_nat := ensure_par;
  extract_nat := extract_parM;
  build_nat := build_parity;
  plus_op := pplusM;
  mult_op := pmultM;
  eq_op := peqM;
  le_op := pleM;
}.

