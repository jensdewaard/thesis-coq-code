Require Import AbstractBool.
Require Import Parity.
Require Import Preorder.

Record IsGalois {A B} (g : B -> A -> Prop)  
                      (e : A->B)
                      (j : B->B->B) 
                      (o : B->B->Prop) :=
{
}.


Class Galois (A B : Type) `{PreorderedSet A} `{PreorderedSet B} : Type :=
{
  gamma : B -> A -> Prop;
  gamma_monotone : forall b b', preorder b b' -> preorder (gamma b) (gamma b');  
}.
Arguments Build_Galois A B {_ _ _ _}.
Arguments gamma {_ _ _ _ _}.


Instance galois_self {A :Type} `{PreorderedSet A} : Galois A A :=
{
  gamma := fun _ _ => True;
}. simpl. constructor. reflexivity.
Defined.

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

Definition gamma_fun {A A' B B' : Type} `{Galois B A} `{Galois B' A'} : 
  (A->A') -> (B -> B') -> Prop :=
  fun f' f => forall b a, gamma b a -> gamma (f' b) (f a).

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
