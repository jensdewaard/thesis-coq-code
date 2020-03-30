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
Require Import Types.Parity.
Require Import Types.State.
Require Import Types.Stores.

Section joinable_functions.
  Context {A B : Type} `{Joinable B}.

  Definition fun_join (f g : A → B) : A → B :=
    λ a : A, (f a) ⊔ (g a).

  Lemma fun_join_idem : ∀ f, fun_join f f = f.
  Proof.
    intro f. unfold fun_join. extensionality a.
    rewrite join_idem. reflexivity.
  Qed.

  Lemma fun_join_assoc : ∀ f g h, 
    fun_join f (fun_join g h) = fun_join (fun_join f g) h.
  Proof.
    intros f g h. unfold fun_join. extensionality a.
    rewrite join_assoc. reflexivity.
  Qed.

  Lemma fun_join_comm : ∀ f g,
    fun_join f g = fun_join g f.
  Proof.
    intros f g. unfold fun_join. extensionality a.
    rewrite join_comm. reflexivity.
  Qed.

  Lemma fun_join_left : ∀ f g,
    f ⊑ (fun_join f g).
  Proof.
    intros f g. unfold preorder; simpl. constructor. intro a.
    unfold fun_join. apply join_upper_bound_left.
  Qed.

  Global Instance functions_joinable : Joinable (A → B) :=
  {
    join_idem := fun_join_idem;
    join_assoc := fun_join_assoc;
    join_comm := fun_join_comm;
    join_upper_bound_left := fun_join_left;
  }.
End joinable_functions.

Definition parity_join (p1 p2 : parity) : parity :=
  match p1, p2 with
  | par_even, par_even => par_even
  | par_odd, par_odd => par_odd
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

Lemma parity_join_idem : ∀ p, parity_join p p = p.
Proof.
  destruct p; reflexivity.
Qed.

Instance parity_joinable : Joinable parity :=
{
  join_idem := parity_join_idem;
  join_upper_bound_left := parity_join_upper_bound_left;
  join_assoc := parity_join_assoc;
  join_comm := parity_join_comm;
}.

Definition abstract_bool_join(b1 b2 : abstr_bool) : abstr_bool :=
  match b1, b2 with
  | ab_true, ab_true => ab_true
  | ab_false, ab_false => ab_false
  | _, _ => ab_top
  end.

Lemma abstract_bool_join_assoc : ∀ b1 b2 b3,
  abstract_bool_join b1 (abstract_bool_join b2 b3) =
  abstract_bool_join (abstract_bool_join b1 b2) b3.
Proof.
  intros. destruct_all abstr_bool; reflexivity.
Qed.

Lemma abstract_bool_join_idem : ∀ b,
  abstract_bool_join b b = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma abstract_bool_join_upper_bound_left : ∀ b1 b2,
  preorder b1 (abstract_bool_join b1 b2).
Proof.
  intros. destruct_all abstr_bool; constructor.
Qed.

Lemma abstract_bool_join_comm : ∀ b1 b2,
  abstract_bool_join b1 b2 = abstract_bool_join b2 b1.
Proof.
  intros. destruct_all abstr_bool; constructor.
Qed.

Instance abstr_bool_joinable : Joinable abstr_bool :=
{
  join_idem := abstract_bool_join_idem;
  join_assoc := abstract_bool_join_assoc;
  join_comm := abstract_bool_join_comm;
  join_upper_bound_left := abstract_bool_join_upper_bound_left;
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

Lemma interval_join_idem : ∀ i,
  interval_join i i = i.
Proof.
  intros. unfold interval_join. destruct i. simpl. apply interval_eq; lia.
Qed.

Lemma interval_join_upper_bound_left : 
  ∀ i1 i2, preorder i1 (interval_join i1 i2).
Proof.
  intros. unfold interval_join. simpl. constructor; simpl; lia.
Qed.

Lemma interval_join_comm : ∀ i j,
  interval_join i j = interval_join j i.
Proof.
  intros. unfold interval_join. simpl. apply interval_eq; lia.
Qed.

Instance interval_joinable : Joinable interval :=
{
  join_idem := interval_join_idem;
  join_assoc := interval_join_assoc;
  join_upper_bound_left := interval_join_upper_bound_left;
  join_comm := interval_join_comm;
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

Lemma avalue_join_idem : ∀ a, avalue_join a a = a.
Proof.
  destruct a; simpl; try rewrite join_idem; reflexivity.
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

Lemma avalue_join_comm : ∀ a1 a2,
  avalue_join a1 a2 = avalue_join a2 a1.
Proof.
  intros. destruct a1, a2; eauto with soundness; simpl; rewrite join_comm;
  reflexivity.
Qed.

Instance avalue_joinable : Joinable avalue :=
{
  join_idem := avalue_join_idem;
  join_assoc := avalue_join_assoc;
  join_upper_bound_left := avalue_join_upper_bound_left;
  join_comm := avalue_join_comm;
}.

Definition abstract_store_join
  (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => join_op (ast1 x) (ast2 x).

Lemma abstract_store_join_idem : ∀ ast,
  abstract_store_join ast ast = ast.
Proof.
  unfold abstract_store_join. intros. ext.
  rewrite join_idem. reflexivity.
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

Lemma abstract_store_join_comm : ∀ s s',
  abstract_store_join s s' = abstract_store_join s' s.
Proof.
  intros. unfold abstract_store_join. ext. rewrite join_comm.
  reflexivity.
Qed.

Global Instance abstract_store_joinable : Joinable abstract_store := {
  join_idem := abstract_store_join_idem;
  join_upper_bound_left := abstract_store_join_upperbound_left;
  join_assoc := abstract_store_join_assoc;
  join_comm := abstract_store_join_comm;
}.

Definition unit_join : unit -> unit -> unit :=
    fun _ _ => tt.
Hint Unfold unit_join : soundness.

Lemma unit_join_upperbound_left : forall (u u' : unit),
  preorder u (unit_join u u').
Proof. simple_solve. Qed.

Lemma unit_join_assoc : ∀ x y z,
  unit_join x (unit_join y z) = unit_join (unit_join x y) z.
Proof.
  reflexivity.
Qed.

Lemma unit_join_idem : ∀ u, unit_join u u = u.
Proof. 
  destruct u. reflexivity.
Qed.

Lemma unit_join_comm : ∀ u v, unit_join u v = unit_join v u.
Proof.
  destruct u, v. reflexivity.
Qed.

Global Instance unit_joinable : Joinable unit :=
{
  join_idem := unit_join_idem;
  join_upper_bound_left := unit_join_upperbound_left;
  join_assoc := unit_join_assoc;
  join_comm := unit_join_comm;
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

  Lemma state_join_assoc : ∀ x y z,
    state_join x (state_join y z) = state_join (state_join x y) z.
  Proof.
    intros. unfold state_join. extensionality a.
    destruct (x a), (y a), (z a); simpl. repeat rewrite join_assoc. 
    reflexivity.
  Qed.

  Lemma state_join_idem : ∀ st,
    state_join st st = st.
  Proof.
    intros. unfold state_join. ext. repeat rewrite join_idem.
    simpl. rewrite <- surjective_pairing. reflexivity.
  Qed.

  Lemma state_join_comm : ∀ st st',
    state_join st st' = state_join st' st.
  Proof.
    intros. unfold state_join. ext. rewrite join_comm. 
    rewrite (join_comm (snd (st x)) _). reflexivity.
  Qed.

  Global Instance state_joinable : Joinable (State S A) := {
    join_idem := state_join_idem;
    join_upper_bound_left := state_join_upper_bound_left;
    join_assoc := state_join_assoc;
    join_comm := state_join_comm;
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

  Lemma identity_join_assoc : ∀ x y z,
    identity_join x (identity_join y z) = identity_join (identity_join x y) z.
  Proof.
    intros. destruct x, y, z; simpl. rewrite join_assoc. reflexivity.
  Qed.

  Lemma identity_join_idem : ∀ x,
    identity_join x x = x.
  Proof. 
    destruct x; simpl. rewrite join_idem. reflexivity. 
  Qed.

  Lemma identity_join_comm : ∀ x y,
    identity_join x y = identity_join y x.
  Proof.
    intros. destruct x, y. unfold identity_join. rewrite join_comm.
    reflexivity.
  Qed.

  Global Instance identity_joinable : Joinable (Identity A) :=
  {
    join_idem := identity_join_idem;
    join_assoc := identity_join_assoc;
    join_upper_bound_left := identity_join_left;
    join_comm := identity_join_comm;
  }.
End identity_joinable.

Section option_joinable.
  Context {A : Type} `{A_joinable : Joinable A}.

  Definition option_join (m n : option A) : option A :=
    match m, n with
    | Some x, Some y => Some (join_op x y)
    | _, _ => None
    end.

  Lemma option_join_left : ∀ m n, preorder m (option_join m n).
  Proof.
    destruct m, n; simpl; auto with soundness. 
  Qed.

  Lemma option_join_assoc : ∀ x y z, 
    option_join x (option_join y z) = option_join (option_join x y) z.
  Proof.
    intros. destruct x, y, z; try reflexivity.
    simpl. rewrite join_assoc. reflexivity.
  Qed.

  Lemma option_join_idem : ∀ m, option_join m m = m.
  Proof.
    destruct m; simpl; try rewrite join_idem; reflexivity.
  Qed.

  Lemma option_join_comm : ∀ x y, option_join x y = option_join y x.
  Proof.
    destruct x, y; simpl. rewrite join_comm. all: reflexivity.
  Qed.

  Global Instance option_joinable : Joinable (option A) :=
  {
    join_idem := option_join_idem;
    join_upper_bound_left := option_join_left;
    join_assoc := option_join_assoc;
    join_comm := option_join_comm;
  }.
End option_joinable.

Section optionA_joinable.
  Context {A : Type} `{A_joinable : Joinable A}.

  Definition optionA_join
    (st1 st2 : optionA A) : optionA A :=
    match st1, st2 with
    | NoneA, NoneA => NoneA
    | SomeA x, SomeA y => SomeA (join_op x y)
    | SomeA x, NoneA | NoneA, SomeA x =>  SomeOrNoneA x
    | NoneA, SomeOrNoneA x | SomeOrNoneA x, NoneA => SomeOrNoneA x
    | SomeA x, SomeOrNoneA y | SomeOrNoneA x, SomeA y => 
        SomeOrNoneA (join_op x y)
    | SomeOrNoneA x, SomeOrNoneA y => SomeOrNoneA (join_op x y)
    end.
  Hint Unfold optionA_join : soundness.

Lemma optionA_join_upperbound_left : forall st st',
  preorder st (optionA_join st st').
Proof. simple_solve. Qed.

Lemma optionA_join_assoc : ∀ x y z : optionA A,
  optionA_join x (optionA_join y z) =
  optionA_join (optionA_join x y) z.
Proof.
  intros. destruct x, y, z; simpl; try reflexivity.
  all: repeat rewrite join_assoc; reflexivity.
Qed.

Lemma optionA_join_idem : ∀ am, 
  optionA_join am am = am.
Proof.
  destruct am; simpl; try rewrite join_idem; reflexivity.
Qed.

Lemma optionA_join_comm : ∀ x y,
  optionA_join x y = optionA_join y x.
Proof.
  intros. destruct x, y; simpl; try rewrite join_comm; reflexivity.
Qed.

Global Instance optionA_joinable : Joinable (optionA A) := 
{
  join_idem := optionA_join_idem;
  join_upper_bound_left := optionA_join_upperbound_left;
  join_assoc := optionA_join_assoc;
  join_comm := optionA_join_comm;
}.
End optionA_joinable.

Section joinable_pairs.
  Context {A B} `{A_joinable : Joinable A, B_joinable : Joinable B}.

  Definition pair_join (p q : (A*B)%type) : (A*B)%type :=
    (join_op (fst p) (fst q), join_op (snd p) (snd q)).

  Lemma pair_join_left : ∀ p q, preorder p (pair_join p q).
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

  Lemma pair_join_idem : ∀ p, pair_join p p = p.
  Proof.
    destruct p. unfold pair_join. simpl. repeat rewrite join_idem.
    reflexivity.
  Qed.

  Lemma pair_join_comm : ∀ p q, pair_join p q = pair_join q p.
  Proof.
    intros. destruct p, q. unfold pair_join. simpl. 
    rewrite (join_comm a0 a). rewrite (join_comm b0 b). reflexivity.
  Qed.

  Global Instance joinable_pairs : Joinable (A*B) :=
  {
    join_idem := pair_join_idem;
    join_upper_bound_left := pair_join_left;
    join_assoc := pair_join_assoc;
    join_comm := pair_join_comm;
  }.
End joinable_pairs.

Section joinable_optionT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T}, 
    Joinable (M T)}.

  Global Instance optionT_joinable {A} `{A_joinable : Joinable A} :
    Joinable (optionT M A) :=
  {
    join_op := join_op;
    join_idem := join_idem;
    join_upper_bound_left := join_upper_bound_left;
    join_assoc := join_assoc;
    join_comm := join_comm;
  }.
End joinable_optionT.

Section joinable_optionAT.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {M_preorder : ∀ T, PreorderedSet (M T)}.
  Context {M_joinable : ∀ T {T_preorder : PreorderedSet T}, 
    Joinable (M T)}.

  Global Instance optionAT_joinable {A} `{A_joinable : Joinable A} : 
    Joinable (optionAT M A) :=
  {
    join_op := join_op;
    join_idem := join_idem;
    join_upper_bound_left := join_upper_bound_left;
    join_assoc := join_assoc;
    join_comm := join_comm;
  }.
End joinable_optionAT.

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

  Lemma stateT_join_assoc : ∀ x y z,
    stateT_join x (stateT_join y z) = stateT_join (stateT_join x y) z.
  Proof.
    intros. unfold stateT_join. ext. rewrite join_assoc. reflexivity.
  Qed.

  Lemma stateT_join_idem : ∀ st,
    stateT_join st st = st.
  Proof.
    intros. unfold stateT_join. ext. rewrite join_idem. reflexivity.
  Qed.

  Lemma stateT_join_comm : ∀ st st',
    stateT_join st st' = stateT_join st' st.
  Proof.
    unfold stateT_join. intros. ext. rewrite join_comm. reflexivity.
  Qed.

  Global Instance stateT_joinable : Joinable (StateT S M A) :=
  {
    join_idem := stateT_join_idem;
    join_upper_bound_left := stateT_join_upper_bound_left;
    join_assoc := stateT_join_assoc;
    join_comm := stateT_join_comm;
  }.
End joinable_stateT.
