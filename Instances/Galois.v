Require Export Base.
Require Import Classes.Galois.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Bool.Bool.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Parity.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

Inductive gamma_par : parity -> nat -> Prop :=
  | gamma_par_even : forall n, even n -> gamma_par par_even n
  | gamma_par_odd  : forall n, odd n -> gamma_par par_odd n
  | gamma_par_top : forall n, gamma_par par_top n.
Hint Constructors gamma_par : soundness.

Lemma gamma_par_monotone : forall p1 p2,
  preorder p1 p2 -> preorder (gamma_par p1) (gamma_par p2).
Proof.
  destruct p1, p2; simpl; intros; try constructor; try inversion H;
  intros; try tauto; constructor; inversion H0.
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


Inductive gamma_interval : interval -> nat -> Prop :=
  | gamma_interval_in_range : 
      forall i n, preorder (min i) n  -> 
                  preorder n (max i) -> 
                  gamma_interval i n.
Hint Constructors gamma_interval : soundness.

Lemma gamma_interval_monotone : monotone gamma_interval.
Proof. 
  intros i i' Hi. constructor. intros n Hn. 
  constructor; destruct Hn; destruct Hi.
  apply preorder_trans with (y:=min i); assumption.
  apply preorder_trans with (y:=max i); assumption.
Qed.

Instance  galois_interval : Galois nat interval :=
{
  gamma := gamma_interval;
  gamma_monotone := gamma_interval_monotone;
}.

Inductive gamma_bool : abstr_bool -> bool -> Prop :=
  | gamma_true : gamma_bool ab_true true
  | gamma_false : gamma_bool ab_false false
  | gamma_ab_top : forall b, gamma_bool ab_top b.
Hint Constructors gamma_bool : soundness.

Lemma gamma_bool_monotone : monotone gamma_bool.
Proof.
  constructor. intros b Hgamma. destruct b. inversion Hgamma; subst.
  inversion H; constructor.
  inversion H; constructor. 
  inversion H; subst; inversion Hgamma; constructor.
Qed.

Instance galois_boolean : Galois bool abstr_bool :=
{
  gamma := gamma_bool;
  gamma_monotone := gamma_bool_monotone;
}.

Section galois_functions.
Context {A A' B B' : Type} 
  `{Galois B A, Galois B' A'}.

Inductive gamma_fun : (A-> A') -> (B -> B') -> Prop :=
  | gamma_fun_increasing : forall (f : A -> A') (f' : B -> B'),
    (forall (a : A) (b : B), gamma a b -> gamma (f a) (f' b)) -> 
    gamma_fun f f'.

Lemma gamma_fun_monotone :
  monotone gamma_fun.
Proof.
  constructor.
  intros x Hgamma. inversion H3; subst. constructor. intros.
  apply widen with (f:= a a0). apply H4. destruct Hgamma.
  apply H6. apply H5.
Qed.

Global Instance GFun : 
  Galois (B -> B') (A->A') :=
{
  gamma := gamma_fun;
  gamma_monotone := gamma_fun_monotone;
}.

End galois_functions.
Hint Constructors gamma_fun : soundness.

Section galois_values.

Inductive gamma_value : avalue -> cvalue -> Prop :=
  | gamma_value_parity : forall p n,
      gamma p n -> gamma_value (VParity p) (VNat n)
  | gamma_value_interval : forall i n,
      gamma i n -> gamma_value (VInterval i) (VNat n)
  | gamma_value_bool : forall ab b,
      gamma ab b -> gamma_value (VAbstrBool ab) (VBool b)
  | gamma_value_top : forall v, gamma_value VTop v.


Lemma gamma_value_monotone : monotone gamma_value.
Proof.
  constructor. intros x Hgamma. inversion Hgamma; subst;
   destruct a'; inversion H; subst; try constructor; try assumption;
    eapply widen; try apply H3; try apply H0.
Qed.

Global Instance galois_values : Galois cvalue avalue := 
{
  gamma := gamma_value;
  gamma_monotone := gamma_value_monotone;
}.
End galois_values.
Hint Constructors gamma_value : soundness.


Inductive gamma_store : abstract_store -> store -> Prop :=
  | gamma_store_cons : forall st st',
      (forall x, gamma (st' x) (st x)) -> gamma_store st' st.
Hint Constructors gamma_store : soundness.

Lemma gamma_store_monotone : monotone gamma_store.
Proof. constructor. intros st Hgamma.
  inversion H; subst. constructor. intros x'. inversion Hgamma; subst.
  apply widen with (f:=a x'); auto.
Qed.

Global Instance galois_store : Galois store abstract_store :=
{
  gamma := gamma_store;
  gamma_monotone := gamma_store_monotone;
}.

Section galois_pairs.
Context {A B C D} `{Galois B A} `{Galois D C}.

Inductive gamma_pairs :
  prod A C-> prod B D -> Prop := 
  | gamma_pairs_cons : forall a b c d,
      gamma a b ->
      gamma c d ->
      gamma_pairs (a,c) (b,d).

Lemma gamma_pairs_monotone :
  monotone gamma_pairs.
Proof.
  constructor. intros [b d] Hgamma. 
  destruct H3 as [a a' c c' Haa' Hcc'].
  inv Hgamma. constructor. 
  - apply widen with (f:=a); auto. 
  - apply widen with (f:=c); auto.
Qed.

Global Instance galois_pairs :
  Galois (B*D) (A*C) :=
{
  gamma := gamma_pairs;
  gamma_monotone := gamma_pairs_monotone;
}.
End galois_pairs.
Hint Constructors gamma_pairs : soundness.

(*
Section galois_result.
Context {A A': Type} `{Galois A' A}.

Inductive gamma_result : abstract_result A abstract_store -> 
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
*)

Section galois_maybe.
  Context {A A'} `{Galois A A'}.

  Inductive gamma_maybe : AbstractMaybe A' -> Maybe A -> Prop :=
    | gamma_none : forall x, gamma_maybe (NoneA) x
    | gamma_justa_just : 
        forall x y, gamma x y -> gamma_maybe (JustA x) (Just y)
    | gamma_justnone_just :
        forall x y, gamma x y -> gamma_maybe (JustOrNoneA x) (Just y)
    | gamma_justnone_none : 
        forall x, gamma_maybe (JustOrNoneA x) (None).

  Lemma gamma_maybe_monotone : monotone gamma_maybe.
  Proof.
    constructor. intros m Hm. destruct m.
    - inversion Hm; subst.
      + destruct a'.
        * inversion H1.
        * inversion H1.
        * constructor.
      + destruct a'.
        * inversion H1; subst. constructor. apply widen with (f:=x).
          assumption. assumption.
        * constructor. inversion H1; subst. apply widen with (f:=x).
          assumption. assumption.
        * constructor.
      + destruct a'.
        * inversion H1.
        * inversion H1; subst. constructor. apply widen with (f:=x).
          assumption. assumption.
        * constructor.
  - inversion Hm; subst; inversion H1; constructor.
  Qed.

  Global Instance galois_maybe : Galois (Maybe A) (AbstractMaybe A') :=
  {
    gamma := gamma_maybe;
    gamma_monotone := gamma_maybe_monotone;
  }.
End galois_maybe.
Hint Constructors gamma_maybe : soundness.

Section galois_state.
Context {A A'} 
  `{Galois A A'}.

Global Instance galois_state :
  Galois (ConcreteState A) (AbstractState A').
Proof.
  apply GFun.
Defined.
End galois_state.


Section galois_unit.
Inductive gamma_unit : 
  unit -> unit -> Prop :=  
    | gamma_unit_tt :  gamma_unit tt tt.


Lemma gamma_unit_monotone : monotone gamma_unit.
Proof.
  unfold monotone.
  intros. simpl. constructor. intros x. destruct a, a', x. reflexivity.
Qed.

Global Instance galois_unit : Galois unit unit := 
{
  gamma := gamma_unit;
  gamma_monotone := gamma_unit_monotone;
}. 
End galois_unit.
Hint Constructors gamma_unit : soundness.


