Require Import Classes.Galois.
Require Import Instances.Galois.Functions.
Require Import Instances.Galois.AbstractStore.
Require Import Instances.Galois.Result.
Require Import Types.State.

Section galois_state.
Context {A A'} 
  `{Galois A A'}.

Global Instance galois_state :
  Galois (State A) (AbstractState A').
Proof.
  apply GFun. 
Defined.
End galois_state.

