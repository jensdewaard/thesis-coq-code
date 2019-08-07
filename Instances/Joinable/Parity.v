Require Import Classes.Joinable.
Require Import Types.Parity.

Definition parity_join (p1 p2 : parity) : parity :=
  match p1, p2 with
  | par_bottom, p | p, par_bottom => p
  | par_top, _ | _, par_top => par_top
  | par_even, par_even => par_even
  | par_odd, par_odd => par_odd
  | par_even, par_odd | par_odd, par_even => par_top 
end.

Lemma parity_join_comm : forall (p1 p2 : parity),
  parity_join p1 p2 = parity_join p2 p1.
Proof. destruct p1, p2; auto. Qed.

Lemma parity_join_assoc : forall (p1 p2 p3 : parity),
  parity_join p1 (parity_join p2 p3) = parity_join (parity_join p1 p2) p3.
Proof. 
    intros. destruct p1, p2, p3; auto.
Qed.

Lemma parity_join_idem : forall (p : parity),
  parity_join p p = p.
Proof. 
  intros. destruct p; auto.
Qed.
  
Lemma parity_join_upperbound_left :
  forall p p', preorder p (parity_join p p').
Proof.
  intros. simpl. unfold parity_join. destruct p, p'; constructor.
Qed.

Lemma parity_join_upperbound_right :
  forall p p', preorder p' (parity_join p p').
Proof.
  intros. simpl. unfold parity_join. destruct p, p'; constructor.
Qed.

Instance parity_joinable : Joinable parity := {
  join_op := parity_join;
  join_upper_bound_left := parity_join_upperbound_left;
  join_upper_bound_right := parity_join_upperbound_right;
}.

