Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Bool.Bool.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Parity.
Require Import Types.Interval.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

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

Definition gamma_interval  (i : interval) (n : nat) : Prop :=
  (preorder (min i) n) /\ (preorder n (max i)).

Lemma gamma_interval_monotone : monotone gamma_interval.
Proof. 
  intros i i' Hi. constructor. intros n Hn. destruct Hn, Hi.
  constructor.
  - eapply preorder_trans. apply H1. apply H.
  - eapply preorder_trans. apply H0. apply H2.
Qed.

Instance  galois_interval : Galois nat interval :=
{
  gamma := gamma_interval;
  gamma_monotone := gamma_interval_monotone;
}.

Definition gamma_bool (ab: abstr_bool) (b : bool) : Prop :=
  match ab with
  | ab_true   => Is_true b
  | ab_false  => ~Is_true b
  | ab_top    => True
  | ab_bottom => False
end.

Lemma gamma_bool_monotone : monotone gamma_bool.
Proof.
  unfold monotone. intros b1 b2 ?.
  destruct b1, b2; constructor; intros; destruct x; simpl in *; 
  try inversion H0; try inversion H; try tauto. 
Qed.

Instance galois_boolean : Galois bool abstr_bool :=
{
  gamma := gamma_bool;
  gamma_monotone := gamma_bool_monotone;
}.

Lemma gamma_false : gamma ab_false false.
Proof.
  unfold gamma; simpl. unfold not. intro. apply H.
Qed.

Section galois_functions.
Context {A A' B B' : Type} 
  `{Galois B A, Galois B' A'}.

Definition gamma_fun (f' : A-> A') (f : B -> B') : 
Prop :=
  forall (a : A) (b : B), gamma a b -> gamma (f' a) (f b).

Lemma gamma_fun_monotone :
  monotone gamma_fun.
Proof.
  constructor.
  intros x Hgamma. unfold gamma_fun in *. 
  intros a0 b Hgamma2.
  apply widen with (f:= a a0). destruct H3; apply H3.
  apply Hgamma. apply Hgamma2.
Qed.

Global Instance GFun : 
  Galois (B -> B') (A->A') :=
{
  gamma := gamma_fun;
  gamma_monotone := gamma_fun_monotone;
}.

End galois_functions.

Section galois_values.

Definition gamma_value : avalue -> cvalue -> Prop :=
  fun av => fun cv => match av, cv with
                      | VParity p, VNat n => gamma p n
                      | VInterval i, VNat n => gamma i n
                      | VAbstrBool ab, VBool b => gamma ab b
                      | VTop, _ => True
                      | _, _ => False
                      end.

Lemma gamma_value_monotone : monotone gamma_value.
Proof.
  unfold monotone. intros a a' Hpre.
  inversion Hpre; subst; constructor; intros z Hgamma; try reflexivity;
  destruct z; try inversion Hgamma; unfold gamma_value; 
  unfold gamma_value in H; eapply widen; try apply H;try apply Hgamma.
Qed.

Global Instance galois_values : Galois cvalue avalue := 
{
  gamma := gamma_value;
  gamma_monotone := gamma_value_monotone;
}.
End galois_values.


Definition gamma_store : abstract_store -> store -> Prop :=
  fun st' => fun st => forall x, gamma (st' x) (st x).

Definition gamma_store_monotone : monotone gamma_store.
Proof. unfold monotone.
  intros ast ast'. simpl. constructor. intros st. unfold gamma_store in *. 
  intros Hgamma x. destruct H. eapply widen. apply H. apply Hgamma.
Qed.

Global Instance galois_store : Galois store abstract_store :=
{
  gamma := gamma_store;
  gamma_monotone := gamma_store_monotone;
}.

Section galois_pairs.
Context {A B C D} `{Galois B A} `{Galois D C}.

Definition gamma_pairs :
  prod A C-> prod B D -> Prop := 
  fun (p1 : A*C) (p2 : B*D) => 
  gamma (fst p1) (fst p2) /\ gamma (snd p1) (snd p2).

Lemma gamma_pairs_monotone :
  monotone gamma_pairs.
Proof.
  unfold monotone. intros [a c] [a' c'].
  intro Hpre. simpl. constructor. intros [b d]. unfold gamma_pairs; simpl.
  intros [Hab Hac]. inversion Hpre; subst. split.
  - eapply widen. apply H6. apply Hab.
  - eapply widen. apply H8. apply Hac. 
Qed.

Global Instance galois_pairs :
  Galois (B*D) (A*C) :=
{
  gamma := gamma_pairs;
  gamma_monotone := gamma_pairs_monotone;
}.
End galois_pairs.

Section galois_result.
Context {A A': Type} `{Galois A' A}.

Definition gamma_result : abstract_result A abstract_store -> 
                          result A' store -> Prop :=
  fun r1 => fun r2 => match r1, r2 with
                      | returnRA a s, returnR b t => 
                          gamma a b /\ gamma s t
                      | crashedA , _ => True
                      | exceptionA st, exception st' => gamma st st'
                      | exceptionOrReturn x st, exception st' =>
                          gamma st st'
                      | exceptionOrReturn x st, returnR x' st' =>
                          gamma st st' /\ gamma x x'
                      | _, _ => False
                      end.

Lemma gamma_result_monotone :
  monotone gamma_result.
Proof.
  unfold monotone. intros a a' Hpred. simpl in *. constructor. 
  intros x Hgamma.
  inversion Hpred; subst.
  - reflexivity.
  - destruct x; try inversion Hgamma.
    eapply widen. apply H1. apply Hgamma.
  - destruct x; try inversion Hgamma.
    split; eapply widen. apply H1. auto. apply H2. auto.
  - destruct x; try inversion Hgamma.
    eapply widen. apply H1. apply Hgamma.
  - destruct x; try inversion Hgamma.
    split; eapply widen. apply H1. apply H4. apply H2. apply H3.
  - destruct x; try inversion Hgamma.
    + split. eapply widen. apply H2. apply H3.
      eapply widen. apply H1. apply H4.
    + eapply widen. apply H2. apply Hgamma.
Qed.

Global Instance galois_result :
  Galois (result A' store) (abstract_result A abstract_store) :=
{
  gamma := gamma_result;
  gamma_monotone := gamma_result_monotone;
}.

End galois_result.

Section galois_state.
Context {A A'} 
  `{Galois A A'}.

Global Instance galois_state :
  Galois (State A) (AbstractState A').
Proof.
  apply GFun. 
Defined.
End galois_state.

Section galois_unit.
Definition gamma_unit : 
  unit -> unit -> Prop :=  
  fun tt tt => True.

Lemma gamma_unit_monotone : monotone gamma_unit.
Proof.
  unfold monotone.
  intros. simpl. constructor. reflexivity.
Qed.

Global Instance galois_unit : Galois unit unit := 
{
  gamma := gamma_unit;
  gamma_monotone := gamma_unit_monotone;
}. 
End galois_unit.

