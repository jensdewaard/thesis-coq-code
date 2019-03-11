Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.

Require Import AbstractBool.
Require Import AbstractStore.
Require Import AbstractInterpreter.
Require Import Aux.
Require Import ConcreteInterpreter.
Require Import Galois.
Require Import Language.
Require Import Maps.
Require Import Parity.
Require Import Preorder.
Open Scope com_scope.

Instance galois_parity_nat : Galois nat parity :=
{
  gamma := gamma_par;
  gamma_monotone := gamma_par_monotone;
}.

Instance galois_boolean : Galois bool abstr_bool :=
{
  gamma := gamma_bool;
  gamma_monotone := gamma_bool_monotone;
}.

Definition sound {A B A' B' : Type} 
  `{Galois A B} `{Galois A' B'}
  (f : A->A') (f' : B->B') :=
  forall b a, gamma b a -> gamma (f' b) (f a).

Definition sound2 {A B : Type} `{Galois A B} (f :A -> A -> A) (f' : B-> B -> B) :=
  forall a1 a2 b1 b2 , gamma b1 a1 -> gamma b2 a2 -> gamma (f' b1 b2) (f a1 a2). 

Theorem sound_parity_plus :
  sound2 plus parity_plus.
Proof.
  unfold sound2; intros. apply parity_plus_sound; assumption.
Qed.

Lemma widen {A A' B:Type} `{Galois B A'}:
  forall (f1 f2 : A->A') (x:A) (a:B),
  pointwise_ordering f1 f2 -> gamma (f1 x) a -> gamma (f2 x) a.
Proof. 
  intros. 
  apply preorder_props with (P:=(gamma (f1 x))) 
    (Q:=(gamma (f2 x))). 
    - apply gamma_monotone. destruct H2. apply H2.
    - apply H3.
Qed.

Definition gamma_fun {A A' B B' : Type} `{Galois B A} `{Galois B' A'} : 
  (A->A') -> (B -> B') -> Prop :=
  fun f' f => forall b a, gamma b a -> gamma (f' b) (f a).

Instance GFun {A A' B B' : Type}
  `{PreorderedSet A} `{PreorderedSet A'}
  `{PreorderedSet B} `{PreorderedSet B'}
  : 
  Galois B A -> Galois B' A' -> Galois (B -> B') (A->A') :=
{
  gamma := gamma_fun;
}.
intros f f'. simpl. constructor. intros f_b. destruct H3. 
intros. unfold gamma_fun in *. intros. 
eapply widen with (f3:=f1). constructor. apply H3. apply H4. apply H5.
Defined.
