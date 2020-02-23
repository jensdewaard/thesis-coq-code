Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Instances.Preorder.
Require Import Language.Statements.
Require Import Psatz.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Maybe.
Require Import Types.Parity.
Require Import Types.State.
Require Import Types.Stores.

Definition parity_join (p1 p2 : parity) : parity :=
  match p1, p2 with
  | par_even, par_even => par_even
  | par_odd, par_odd => par_odd
  | par_bottom, par_bottom => par_bottom
  | par_even, par_bottom | par_bottom, par_even => par_even
  | par_odd, par_bottom | par_bottom, par_odd => par_odd
  | _, _ => par_top
  end.

Lemma parity_join_comm : ∀ p1 p2,
  parity_join p1 p2 = parity_join p2 p1.
Proof.
  destruct p1, p2; reflexivity.
Qed.

Lemma parity_join_assoc : ∀ p1 p2 p3,
  parity_join p1 (parity_join p2 p3) = parity_join (parity_join p1 p2) p3.
Proof.
  intros. destruct_all parity; reflexivity.
Qed.

Lemma parity_join_upper_bound_left :
  ∀ p1 p2, preorder p1 (parity_join p1 p2).
Proof.
  intros. destruct_all parity; constructor.
Qed.

Lemma parity_join_upper_bound_right :
  ∀ p1 p2, preorder p2 (parity_join p1 p2).
Proof.
  intros. destruct_all parity; constructor.
Qed.

Lemma parity_join_refl : ∀ p, parity_join p p = p.
Proof.
  destruct p; reflexivity.
Qed.

Instance parity_joinable : Joinable parity :=
{
  join_refl := parity_join_refl;
  join_upper_bound_left := parity_join_upper_bound_left;
  join_upper_bound_right := parity_join_upper_bound_right;
  join_assoc := parity_join_assoc;
}.

Definition abstract_bool_join(b1 b2 : abstr_bool) : abstr_bool :=
  match b1, b2 with
  | ab_true, ab_true => ab_true
  | ab_false, ab_false => ab_false
  | ab_true, ab_bottom | ab_bottom, ab_true => ab_true
  | ab_false, ab_bottom | ab_bottom, ab_false => ab_false
  | ab_bottom, ab_bottom => ab_bottom
  | ab_true, ab_false | ab_false, ab_true => ab_top
  | ab_top, _ | _, ab_top => ab_top
  end.

Lemma abstract_bool_join_assoc : ∀ b1 b2 b3,
  abstract_bool_join b1 (abstract_bool_join b2 b3) =
  abstract_bool_join (abstract_bool_join b1 b2) b3.
Proof.
  intros. destruct_all abstr_bool; reflexivity.
Qed.

Lemma abstract_bool_join_refl : ∀ b,
  abstract_bool_join b b = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma abstract_bool_join_upper_bound_left : ∀ b1 b2,
  preorder b1 (abstract_bool_join b1 b2).
Proof.
  intros. destruct_all abstr_bool; constructor.
Qed.

Lemma abstract_bool_join_upper_bound_right : ∀ b1 b2,
  preorder b2 (abstract_bool_join b1 b2).
Proof.
  intros. destruct_all abstr_bool; constructor.
Qed.

Instance abstr_bool_joinable : Joinable abstr_bool :=
{
  join_refl := abstract_bool_join_refl;
  join_assoc := abstract_bool_join_assoc;
  join_upper_bound_left := abstract_bool_join_upper_bound_left;
  join_upper_bound_right := abstract_bool_join_upper_bound_right;
}.

Lemma nat_min_min_max_max : ∀ i j,
  Nat.min (min i) (min j) ≤ Nat.max (max i) (max j).
Proof.
  intros. destruct i, j; simpl. lia.
Qed.

Definition interval_join (i j : interval) : interval :=
  Interval (Nat.min (min i) (min j)) 
           (Nat.max (max i) (max j)) 
           (nat_min_min_max_max i j).

Lemma interval_join_assoc : ∀ i1 i2 i3,
  interval_join i1 (interval_join i2 i3) =
  interval_join (interval_join i1 i2) i3.
Proof.
  intros. unfold interval_join. simpl. 
  apply interval_eq. rewrite Nat.min_assoc. reflexivity.
  rewrite Nat.max_assoc. reflexivity.
Qed.

Lemma interval_join_refl : ∀ i,
  interval_join i i = i.
Proof.
  intros. unfold interval_join. destruct i. simpl.
  apply interval_eq. apply Nat.min_idempotent. apply Nat.max_idempotent.
Qed.

Lemma interval_join_upper_bound_left : 
  ∀ i1 i2, preorder i1 (interval_join i1 i2).
Proof.
  intros. unfold interval_join. simpl. constructor; simpl; lia.
Qed.

Lemma interval_join_upper_bound_right :
  ∀ i1 i2, preorder i2 (interval_join i1 i2).
Proof.
  intros. unfold interval_join. constructor; simpl; lia.
Qed.

Instance interval_joinable : Joinable interval :=
{
  join_refl := interval_join_refl;
  join_assoc := interval_join_assoc;
  join_upper_bound_left := interval_join_upper_bound_left;
  join_upper_bound_right := interval_join_upper_bound_right;
}.

Definition avalue_join (a1 a2 : avalue) : avalue :=
  match a1, a2 with
  | VParity p1, VParity p2 => VParity (join_op p1 p2)
  | VParity _, VAbstrBool _ | VAbstrBool _, VParity _ => VTop
  | VParity _, VInterval _ | VInterval _, VParity _ => VTop
  | VParity _, VTop | VTop, VParity _ => VTop
  | VParity x, VBottom | VBottom, VParity x => VParity x
  | VAbstrBool b1, VAbstrBool b2 => VAbstrBool (join_op b1 b2)
  | VAbstrBool _, VInterval _ | VInterval _, VAbstrBool _ => VTop
  | VAbstrBool _, VTop | VTop, VAbstrBool _ => VTop
  | VAbstrBool b, VBottom | VBottom, VAbstrBool b => VAbstrBool b
  | VInterval i1, VInterval i2 => VInterval (join_op i1 i2)
  | VInterval _, VTop | VTop, VInterval _ => VTop
  | VInterval i, VBottom | VBottom, VInterval i => VInterval i
  | VTop, VTop => VTop
  | VTop, VBottom | VBottom, VTop => VTop
  | VBottom, VBottom => VBottom
  end.

Lemma avalue_join_refl : ∀ a, avalue_join a a = a.
Proof.
  destruct a; simpl; try rewrite join_refl; reflexivity.
Qed.

Lemma avalue_join_assoc : ∀ a1 a2 a3,
  avalue_join a1 (avalue_join a2 a3) = avalue_join (avalue_join a1 a2) a3.
Proof.
  intros. destruct_all avalue; simpl; try rewrite join_assoc; reflexivity.
Qed.
  
Lemma avalue_join_upper_bound_left : ∀ a1 a2,
  preorder a1 (avalue_join a1 a2).
Proof. 
  intros. destruct a1, a2; eauto with soundness.
Qed.

Lemma avalue_join_upper_bound_right : ∀ a1 a2,
  preorder a2 (avalue_join a1 a2).
Proof. 
  intros. destruct a1, a2; eauto with soundness.
Qed.

Instance avalue_joinable : Joinable avalue :=
{
  join_refl := avalue_join_refl;
  join_assoc := avalue_join_assoc;
  join_upper_bound_left := avalue_join_upper_bound_left;
  join_upper_bound_right := avalue_join_upper_bound_right;
}.

Definition abstract_store_join
  (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => join_op (ast1 x) (ast2 x).

Lemma abstract_store_join_refl : ∀ ast,
  abstract_store_join ast ast = ast.
Proof.
  unfold abstract_store_join. intros. ext.
  rewrite join_refl. reflexivity.
Qed.

Lemma abstract_store_join_assoc : forall ast1 ast2 ast3,
  abstract_store_join ast1 (abstract_store_join ast2 ast3) =
  abstract_store_join (abstract_store_join ast1 ast2) ast3.
Proof. 
  intros. unfold abstract_store_join. ext. rewrite join_assoc.
  reflexivity.
Qed.

Lemma abstract_store_join_upperbound_left :
    forall s s', preorder s (abstract_store_join s s').
Proof. 
  eauto with soundness.
Qed.

Lemma abstract_store_join_upperbound_right : 
  forall s s', preorder s' (abstract_store_join s s').
Proof. eauto with soundness. Qed.

Global Instance abstract_store_joinable : Joinable abstract_store := {
  join_refl := abstract_store_join_refl;
  join_upper_bound_left := abstract_store_join_upperbound_left;
  join_upper_bound_right := abstract_store_join_upperbound_right;
  join_assoc := abstract_store_join_assoc;
}.

Definition unit_join : unit -> unit -> unit :=
    fun _ _ => tt.
Hint Unfold unit_join : soundness.

Lemma unit_join_upperbound_left : forall (u u' : unit),
  preorder u (unit_join u u').
Proof. simple_solve. Qed.

Lemma unit_join_upperbound_right : forall (u u' : unit),
  preorder u' (unit_join u u').
Proof. simple_solve. Qed.

Lemma unit_join_assoc : ∀ x y z,
  unit_join x (unit_join y z) = unit_join (unit_join x y) z.
Proof.
  reflexivity.
Qed.

Lemma unit_join_refl : ∀ u, unit_join u u = u.
Proof. 
  destruct u. reflexivity.
Qed.

Global Instance unit_joinable : Joinable unit :=
{
  join_refl := unit_join_refl;
  join_upper_bound_left := unit_join_upperbound_left;
  join_upper_bound_right := unit_join_upperbound_right;
  join_assoc := unit_join_assoc;
}.

Section state_joinable.
  Context {S A} `{S_joinable : Joinable S, A_joinable : Joinable A}.

  Definition state_join (st st' : State S A) : State S A :=
    fun x => ((join_op (fst (st x)) (fst (st' x)), 
              (join_op (snd (st x)) (snd (st' x))))).
  Hint Unfold state_join : soundness.
  
  Lemma state_join_upper_bound_left :
    forall st st', preorder st (state_join st st').
  Proof. 
    intros st st'. unfold state_join.
    simpl. constructor. intro x. destruct (st x). 
    constructor; eauto with soundness.
  Qed.

  Lemma state_join_upper_bound_right :
    forall st st', preorder st' (state_join st st').
  Proof. 
    intros st st'. unfold state_join. constructor.
    intro x. destruct (st' x). constructor; eauto with soundness.
  Qed.

  Lemma state_join_assoc : ∀ x y z,
    state_join x (state_join y z) = state_join (state_join x y) z.
  Proof.
    intros. unfold state_join. extensionality a.
    destruct (x a), (y a), (z a); simpl. repeat rewrite join_assoc. 
    reflexivity.
  Qed.

  Lemma state_join_refl : ∀ st,
    state_join st st = st.
  Proof.
    intros. unfold state_join. ext. repeat rewrite join_refl.
    simpl. rewrite <- surjective_pairing. reflexivity.
  Qed.

  Global Instance state_joinable : Joinable (State S A) := {
    join_refl := state_join_refl;
    join_upper_bound_left := state_join_upper_bound_left;
    join_upper_bound_right := state_join_upper_bound_right;
    join_assoc := state_join_assoc;
  }.
End state_joinable.

Section identity_joinable.
  Context {A : Type} `{Joinable A}.

  Definition identity_join (i j : Identity A) : Identity A :=
    match i, j with
    | identity a, identity a' => identity (join_op a a')
    end.

  Lemma identity_join_left : ∀ i j, preorder i (identity_join i j).
  Proof.
    destruct i, j. simpl. apply join_upper_bound_left.
  Qed.

  Lemma identity_join_right : ∀ i j, preorder j (identity_join i j).
  Proof.
    destruct i, j; simpl. apply join_upper_bound_right.
  Qed.

  Lemma identity_join_assoc : ∀ x y z,
    identity_join x (identity_join y z) = identity_join (identity_join x y) z.
  Proof.
    intros. destruct x, y, z; simpl. rewrite join_assoc. reflexivity.
  Qed.

  Lemma identity_join_refl : ∀ x,
    identity_join x x = x.
  Proof. 
    destruct x; simpl. rewrite join_refl. reflexivity. 
  Qed.

  Global Instance identity_joinable : Joinable (Identity A) :=
  {
    join_refl := identity_join_refl;
    join_assoc := identity_join_assoc;
    join_upper_bound_left := identity_join_left;
    join_upper_bound_right := identity_join_right;
  }.
End identity_joinable.

Section maybe_joinable.
  Context {A : Type} `{A_joinable : Joinable A}.

  Definition maybe_join (m n : Maybe A) : Maybe A :=
    match m, n with
    | Just x, Just y => Just (join_op x y)
    | _, _ => None
    end.

  Lemma maybe_join_left : ∀ m n, preorder m (maybe_join m n).
  Proof.
    destruct m, n; simpl; auto with soundness. 
  Qed.

  Lemma maybe_join_right : ∀ m n, preorder n (maybe_join m n).
  Proof. destruct m, n; simpl; auto with soundness. Qed.

  Lemma maybe_join_assoc : ∀ x y z, 
    maybe_join x (maybe_join y z) = maybe_join (maybe_join x y) z.
  Proof.
    intros. destruct x, y, z; try reflexivity.
    simpl. rewrite join_assoc. reflexivity.
  Qed.

  Lemma maybe_join_refl : ∀ m, maybe_join m m = m.
  Proof.
    destruct m; simpl; try rewrite join_refl; reflexivity.
  Qed.

  Global Instance maybe_joinable : Joinable (Maybe A) :=
  {
    join_refl := maybe_join_refl;
    join_upper_bound_left := maybe_join_left;
    join_upper_bound_right := maybe_join_right;
    join_assoc := maybe_join_assoc;
  }.
End maybe_joinable.

Section abstract_maybe_joinable.
Context {A : Type} `{A_joinable : Joinable A}.

Definition abstract_maybe_join
  (st1 st2 : AbstractMaybe A) : AbstractMaybe A :=
  match st1, st2 with
  | NoneA, NoneA => NoneA
  | JustA x, JustA y => JustA (join_op x y)
  | JustA x, NoneA | NoneA, JustA x =>  JustOrNoneA x
  | NoneA, JustOrNoneA x | JustOrNoneA x, NoneA => JustOrNoneA x
  | JustA x, JustOrNoneA y | JustOrNoneA x, JustA y => 
      JustOrNoneA (join_op x y)
  | JustOrNoneA x, JustOrNoneA y => JustOrNoneA (join_op x y)
  end.
Hint Unfold abstract_maybe_join : soundness.

Lemma abstract_maybe_join_upperbound_left : forall st st',
  preorder st (abstract_maybe_join st st').
Proof. simple_solve. Qed.

Lemma abstract_maybe_join_upperbound_right : forall st st',
  preorder st' (abstract_maybe_join st st').
Proof. simple_solve. Qed.

Lemma abstract_maybe_join_assoc : ∀ x y z : AbstractMaybe A,
  abstract_maybe_join x (abstract_maybe_join y z) =
  abstract_maybe_join (abstract_maybe_join x y) z.
Proof.
  intros. destruct x, y, z; simpl; try reflexivity.
  all: repeat rewrite join_assoc; reflexivity.
Qed.

Lemma abstract_maybe_join_refl : ∀ am, 
  abstract_maybe_join am am = am.
Proof.
  destruct am; simpl; try rewrite join_refl; reflexivity.
Qed.

Global Instance abstract_maybe_joinable : Joinable (AbstractMaybe A) := 
{
  join_refl := abstract_maybe_join_refl;
  join_upper_bound_left := abstract_maybe_join_upperbound_left;
  join_upper_bound_right := abstract_maybe_join_upperbound_right;
  join_assoc := abstract_maybe_join_assoc;
}.
End abstract_maybe_joinable.

Section joinable_pairs.
  Context {A B} `{A_joinable : Joinable A, B_joinable : Joinable B}.

  Definition pair_join (p q : (A*B)%type) : (A*B)%type :=
    (join_op (fst p) (fst q), join_op (snd p) (snd q)).

  Lemma pair_join_left : ∀ p q, preorder p (pair_join p q).
  Proof.
    destruct p, q. eauto with soundness.
  Qed.

  Lemma pair_join_right : ∀ p q, preorder q (pair_join p q).
  Proof.
    destruct p, q. eauto with soundness.
  Qed.

  Lemma pair_join_assoc : ∀ x y z, 
    pair_join x (pair_join y z) = pair_join (pair_join x y) z.
  Proof.
    intros. destruct x as [x1 x2], y as [y1 y2], z as [z1 z2]. 
    unfold pair_join; simpl. repeat rewrite join_assoc.
    reflexivity.
  Qed.

  Lemma pair_join_refl : ∀ p, pair_join p p = p.
  Proof.
    destruct p. unfold pair_join. simpl. repeat rewrite join_refl.
    reflexivity.
  Qed.

  Global Instance joinable_pairs : Joinable (A*B) :=
  {
    join_refl := pair_join_refl;
    join_upper_bound_left := pair_join_left;
    join_upper_bound_right := pair_join_right;
    join_assoc := pair_join_assoc;
  }.
End joinable_pairs.

Section joinable_maybeT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T}, 
    Joinable (M T)}.

  Global Instance maybeT_joinable {A} `{A_joinable : Joinable A} :
    Joinable (MaybeT M A) :=
  {
    join_op := join_op;
    join_refl := join_refl;
    join_upper_bound_left := join_upper_bound_left;
    join_upper_bound_right := join_upper_bound_right;
    join_assoc := join_assoc;
  }.
End joinable_maybeT.

Section joinable_maybeAT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T}, 
    Joinable (M T)}.

  Global Instance maybeAT_joinable {A} `{A_joinable : Joinable A} : 
    Joinable (MaybeAT M A) :=
  {
    join_op := join_op;
    join_refl := join_refl;
    join_upper_bound_left := join_upper_bound_left;
    join_upper_bound_right := join_upper_bound_right;
    join_assoc := join_assoc;
  }.
End joinable_maybeAT.

Section joinable_stateT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {S A : Type} `{S_joinable : Joinable S, A_joinable : Joinable A}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T},
    Joinable (M T)}.

  Definition stateT_join (st st' : StateT S M A) : StateT S M A :=
    λ x, join_op (st x) (st' x).

  Lemma stateT_join_upper_bound_left : ∀ t t' : StateT S M A,
    preorder t (stateT_join t t').
  Proof.
    intros. unfold stateT_join. constructor. intros. 
    apply join_upper_bound_left.
  Qed.

  Lemma stateT_join_upper_bound_right : ∀ t t' : StateT S M A, 
    preorder t' (stateT_join t t').
  Proof.
    intros. unfold stateT_join. constructor. intros.
    apply join_upper_bound_right.
  Qed.

  Lemma stateT_join_assoc : ∀ x y z,
    stateT_join x (stateT_join y z) = stateT_join (stateT_join x y) z.
  Proof.
    intros. unfold stateT_join. ext. rewrite join_assoc. reflexivity.
  Qed.

  Lemma stateT_join_refl : ∀ st,
    stateT_join st st = st.
  Proof.
    intros. unfold stateT_join. ext. rewrite join_refl. reflexivity.
  Qed.

  Global Instance stateT_joinable : Joinable (StateT S M A) :=
  {
    join_refl := stateT_join_refl;
    join_upper_bound_left := stateT_join_upper_bound_left;
    join_upper_bound_right := stateT_join_upper_bound_right;
    join_assoc := stateT_join_assoc;
  }.
End joinable_stateT.
