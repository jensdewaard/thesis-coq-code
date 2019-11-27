(* State and AbstractStates *)

Require Import Classes.PreorderedSet.
Require Import Instances.Preorder.
Require Import Types.Stores.
Require Import Instances.Monad.

Definition ConcreteState := MaybeT (StateT store Maybe ).


Definition AbstractState := 
  MaybeAT (StateT abstract_store Maybe).

Section preorder.
  Context {A} `{PreorderedSet A}.

  Global Instance preorder_abstract_state : PreorderedSet (AbstractState A).
  Proof.
    apply statet_preorder.
  Defined.
End preorder.


