Require Export Base.
Require Import Arith Coq.Arith.Le Coq.Arith.Mult Coq.Arith.PeanoNat
  Coq.Arith.Plus Psatz Types.AbstractBool Classes.PreorderedSet
  Classes.Joinable Classes.Galois.
From Coq Require Export EqdepFacts.

Record interval := Interval {
  min: nat;
  max : nat;
  min_max : min <= max;
}.

Notation "[ x , y ]" := (@Interval x y _).

Lemma nat_le_pi : ∀ x y (H1 H2 : x ≤ y), H1 = H2.
Proof.
  assert (∀ x y (p : x ≤ y) y' (q : x ≤ y'),
  y = y' → eq_dep nat (le x) y p y' q) as aux.
  { fix FIX 3. intros x ? [|y p] ? [|y' q].
  - constructor.
  - clear FIX. intros; exfalso; lia.
  - clear FIX. intros; exfalso; lia.
  - injection 1. intros Hy. case (FIX x
    y p y' q Hy); constructor. }
  intros x y p q.
  apply (Eqdep_dec.eq_dep_eq_dec eq_nat_dec), aux.
  reflexivity.
Qed.

Lemma plus_min_max : ∀ i1 i2, 
  min i1 + min i2 ≤ max i1 + max i2.
Proof.
  destruct i1, i2; simpl. lia.
Qed.

Lemma interval_eq i1 i2 j1 j2 H1 H2 :
     i1 = i2 → j1 = j2 →
        Interval i1 j1 H1 = Interval i2 j2 H2.
Proof. 
  intros -> ->. 
  f_equal. apply nat_le_pi. 
Qed.

Definition iplus (i1 i2 : interval) : interval := 
  Interval ((min i1) + (min i2)) ((max i1) + (max i2)) (plus_min_max i1 i2).

Lemma mult_min_max : ∀ i1 i2,
  min i1 * min i2 ≤ max i1 * max i2.
Proof.
  destruct i1, i2; simpl. 
  apply Nat.mul_le_mono; assumption.
Qed.

Definition imult (i1 i2 : interval) : interval :=
  Interval ((min i1) * (min i2)) ((max i1) * (max i2)) (mult_min_max i1 i2).

Definition ieqb (i1 i2 : interval) : (abstr_bool+⊤) :=
  if (Nat.ltb (max i1) (min i2)) then
    NotTop ab_false
  else if (andb (andb (Nat.eqb (min i1) (max i1)) 
                      (Nat.eqb (max i1) (min i2))) 
                (Nat.eqb (min i2) (max i2))) then
           NotTop ab_true
  else Top.

Definition ileqb (i1 i2 : interval) : (abstr_bool+⊤) :=
  if (Nat.ltb (max i1) (min i2)) then
    NotTop ab_true
  else if (Nat.ltb (max i2) (min i1)) then
    NotTop ab_false
  else
    Top.

Lemma interval_min_mult : forall i j,
  min (imult i j) = min i * min j.
Proof. 
  intros. unfold imult. simpl. reflexivity.
Qed.

Lemma interval_max_mult : forall i j,
  max (imult i j) = max i * max j.
Proof. 
  intros. unfold imult. simpl. reflexivity.
Qed.

Lemma nat_min_min_max_max : ∀ i j,
  Nat.min (min i) (min j) ≤ Nat.max (max i) (max j).
Proof.
  intros. destruct i, j; simpl. lia.
Qed.

Inductive interval_le : interval → interval → Prop :=
  | interva_le_cons : ∀ i j,
      preorder (min j) (min i) → preorder (max i) (max j) →
      interval_le i j.
Hint Constructors interval_le : preorders.

Global Instance preorder_interval : PreorderedSet interval.
Proof. proof_preorder interval_le. Defined.

Instance interval_joinable : Joinable interval interval :=
  λ i, λ j, Interval (Nat.min (min i) (min j)) 
           (Nat.max (max i) (max j)) 
           (nat_min_min_max_max i j).

Inductive gamma_interval : interval → nat → Prop :=
  | gamma_interval_cons : ∀ i n, 
      preorder (min i) n → preorder n (max i) → gamma_interval i n.

Instance galois_interval : Galois interval nat := gamma_interval.

Lemma n_eq_interval : ∀ n, n <= n.
Proof. auto. Qed.

Instance extract_interval : extract_op nat interval := λ n, 
  Interval n n (n_eq_interval n).

Instance extract_interval_sound : 
  extract_op_sound extract_interval extract_nat.
Proof.
  intro n. unfold extract, extract_nat, extract_interval. rewrite id_refl.
  constructor; constructor.
Qed.
Hint Resolve extract_interval_sound : soundness.

Instance preorder_interval_sound : PreorderSound interval nat.
Proof.
  intros x y Hpre n Hgamma. destruct x, y; eauto with soundness. 
  inversion Hpre; subst; clear Hpre. 
  gamma_destruct. simpl in *. constructor; simpl; lia.
Qed.

Instance join_interval_nat_sound : JoinableSound interval_joinable.
Proof.
  split; destruct x as [Xmin Xmax], y as [Ymin Ymax]; simpl in *.
  - destruct H. 
    + inversion H; subst; simpl in *; clear H.
      apply le_trans with Xmin. apply Nat.le_min_l. assumption.
    + inversion H; subst; simpl in *; clear H.
      apply le_trans with Ymin. apply Nat.le_min_r. assumption.
  - destruct H.
    + inversion H; subst; simpl in *; clear H.
      apply le_trans with Xmax. assumption. apply Nat.le_max_l.
    + inversion H; subst; simpl in *; clear H.
      apply le_trans with Ymax. assumption. apply Nat.le_max_r.
Qed.

