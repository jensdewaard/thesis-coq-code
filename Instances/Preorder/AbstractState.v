Require Import Classes.PreorderedSet.
Require Import Types.State.
Require Import Instances.Preorder.Functions.

Section preordered_abstract_state.
Context {A : Type} `{PreorderedSet A}.

Lemma preorder_abstract_state : PreorderedSet (AbstractState A).
Proof.
  intros. 
  apply preordered_function_spaces.
Qed.

End preordered_abstract_state.
