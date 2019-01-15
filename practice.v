Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import Parity.

Inductive cexp : Type :=
  | CNum : nat -> cexp
  | CVar : cexp
  | CPlus : cexp -> cexp -> cexp
  | CMult : cexp -> cexp -> cexp.

(* Find some way to define eval and abstract_eval on the same 
   set of commands; but how then to incorporate that they will
   have to work with different values (x and x^)?

   Or have separate expressions like currently implemented, but
   how to estabilish "equivelance" between APlus and CPlus? *)

Fixpoint eval (e : cexp) (x : nat) : nat := 
  match e with
  | CNum n => n
  | CVar => x
  | CPlus e1 e2 => eval e1 x + eval e2 x
  | CMult e1 e2 => eval e1 x * eval e2 x
  end.

Fixpoint abstract_eval (e : cexp) (p : parity) : parity :=
  match e with 
  | CNum n => extract n
  | CVar => p
  | CPlus p1 p2 => parity_plus (abstract_eval p1 p) (abstract_eval p2 p)
  | CMult p1 p2 => parity_mult (abstract_eval p1 p) (abstract_eval p2 p)
  end.

Inductive isNumber : nat -> Prop :=
  | nIsNumber : forall n, isNumber n.

Inductive noNumber : nat -> Prop :=.

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

Lemma abstract_plus_sound : forall e1 e2 p n,
  gamma (abstract_eval e1 p) (eval e1 n) ->
  gamma (abstract_eval e2 p) (eval e2 n) ->
  gamma (abstract_eval (CPlus e1 e2) p) (eval (CPlus e1 e2) n).
Proof.
  intros. simpl. apply gamma_distr_plus; assumption.
Qed.

Lemma abstract_mult_sound : forall e1 e2 p n,
  gamma (abstract_eval e1 p) (eval e1 n) ->
  gamma (abstract_eval e2 p) (eval e2 n) ->
  gamma (abstract_eval (CMult e1 e2) p) (eval (CMult e1 e2) n).
Proof. intros. simpl. apply gamma_distr_mult; assumption.
Qed.

Theorem abstract_eval_sound : forall e p n,
  (gamma p) n ->
  (gamma (abstract_eval e p)) (eval e n).
Proof.
  induction e; intros.
  - (* CNum *)
    simpl. apply gamma_extract_n_n.
  - (* CVar *)
    simpl. assumption.
  - (* CPlus *)
    apply abstract_plus_sound; auto.
    - (* CMult *)
    apply abstract_mult_sound; auto.
Qed.
(* proof the equivalance of the galois connection diagram *)
(* Peval o gamma \subset gamma o abstract_eval *)
(* etc... *)

(* refactor the above code (and finish the proofs) *)
(* implement multiple variables, with store (nat -> nat) *)
(* Add a statements SKIP, sequencing, if statements, assignment *)

