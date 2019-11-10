(* State and AbstractStates *)

Require Import Classes.Joinable.
Require Import Classes.PreorderedSet.
Require Import Instances.Joinable.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.Monad.
Require Import Types.Result.
Require Import Types.Stores.
Require Import Types.Maps.
Require Import Instances.Monad.
Require Import FunctionalExtensionality.

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


