(* Some auxiliary lemma's, defined here so not to lost overview of
   what we're actually trying to prove *)

Lemma add_succ_r : forall n m,
  n + S m = S(n + m).
Proof.
  induction n. 
  - reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.


