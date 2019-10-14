Require Import Types.AbstractBool.

Definition interval := (nat * nat) % type.

Definition min (i : interval) : nat := min (fst i) (snd i).
Definition max (i : interval) : nat := max (fst i) (snd i).

Definition iplus (i1 i2 : interval) : interval := 
  ((min i1) + (min i2), (max i1) + (max i2)).

Definition imult (i1 i2 : interval) : interval :=
  ((min i1) * (min i2), (max i1) * (max i2)).

Definition ieqb (i1 i2 : interval) : abstr_bool :=
  if (Nat.ltb (max i1) (min i2)) then
    ab_false
  else if (andb (andb (Nat.eqb (min i1) (max i1)) 
                      (Nat.eqb (max i1) (min i2))) 
                (Nat.eqb (min i2) (max i2))) then
           ab_true
  else ab_top.

Definition ileqb (i1 i2 : interval) : abstr_bool :=
  if (Nat.ltb (max i1) (min i2)) then
    ab_true
  else if (Nat.ltb (max i2) (min i1)) then
    ab_false
  else
    ab_top.

Require Import Coq.Arith.Le.
Lemma interval_increasing : forall i,
  min i <= max i.
Proof with auto with arith.
  destruct i as [n m]. unfold min, max. simpl.
  generalize dependent n.
  induction m...
  - intro n. induction n...
  - induction n... simpl. apply le_n_S. apply IHm.
Qed.


