Require Import Types.AbstractBool.

Definition interval := (nat * nat) % type.

Definition iplus (i1 i2 : interval) : interval := 
  ((fst i1) + (fst i2), (snd i1) + (snd i2)).

Definition imult (i1 i2 : interval) : interval :=
  ((fst i1) * (fst i2), (snd i1) * (snd i2)).

Definition ieqb (i1 i2 : interval) : abstr_bool :=
  if (Nat.ltb (snd i1) (fst i2)) then
    ab_false
  else if (andb (andb (Nat.eqb (fst i1) (snd i1)) 
                      (Nat.eqb (snd i1) (fst i2))) 
                (Nat.eqb (fst i2) (snd i2))) then
           ab_true
  else ab_top.

Definition ileqb (i1 i2 : interval) : abstr_bool :=
  if (Nat.ltb (snd i1) (fst i2)) then
    ab_true
  else if (Nat.ltb (snd i2) (fst i1)) then
    ab_false
  else
    ab_top.


