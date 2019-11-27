Require Import Types.Stores.
Require Import Instances.Monad.

Definition ConcreteState := MaybeT (StateT store Maybe ).


Definition AbstractState := 
  MaybeAT (StateT abstract_store Maybe).
