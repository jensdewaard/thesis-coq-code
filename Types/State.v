Require Import Types.Stores.
Require Import Instances.Monad.

Definition ConcreteState := MaybeT (StateT store Maybe).

Definition AbstractState := 
  MaybeAT (StateT abstract_store Maybe).

Definition concrete_state_maybe := StateT store Maybe.
Definition abstract_state_maybe := StateT abstract_store Maybe.
