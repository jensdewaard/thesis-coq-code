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
}.
- intros b b' H'. simpl. constructor.  reflexivity.
Defined.

