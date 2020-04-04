Require Export Base.
Require Import Classes.Galois.

Class Joinable (A B : Type) : Type :=
{
  join_op : A -> A -> B;
  join_comm : ∀ x y, join_op x y = join_op y x;
}.
Arguments join_op : simpl never.
Infix "⊔" := join_op (at level 40).

Class JoinableSound (A B C : Type) 
  `{Joinable A B} `{Galois A C} `{Galois B C} : Prop :=
  join_sound : ∀ x y : A, γ x ∪ γ y ⊆ γ (x ⊔ y).

Section joinable_functions.
  Context {A B : Type} `{Joinable B B}.

  Definition fun_join (f g : A → B) : A → B :=
    λ a : A, (f a) ⊔ (g a).

  Lemma fun_join_comm : ∀ f g,
    fun_join f g = fun_join g f.
  Proof.
    intros f g. unfold fun_join. extensionality a.
    rewrite join_comm. reflexivity.
  Qed.

  Global Instance functions_joinable : Joinable (A → B) (A → B) :=
  {
    join_comm := fun_join_comm;
  }.
End joinable_functions.

Section joinable_top_l.
  Context (A : Type) `{Joinable A (A+⊤)}.

  Definition top_join (a a' : A+⊤) : A+⊤ :=
    match a, a' with
    | NotTop x, NotTop y => x ⊔ y
    | _, _ => Top
    end.

  Global Instance top_joinable_l : Joinable (A+⊤) (A+⊤).
  Proof.
    split with (top_join). intros x y.
    destruct x, y; simpl. 4: rewrite join_comm. 
    all: reflexivity.
  Defined.
End joinable_top_l.

Section joinable_top_r.
  Context (A : Type) `{AJ : Joinable A A}.

  Definition top_join_r (a a' : A) : A+⊤ := NotTop (a ⊔ a').

  Global Instance top_joinable_r : Joinable A (A+⊤).
  Proof.
    split with top_join_r. intros. unfold top_join_r. rewrite join_comm.
    reflexivity.
  Defined.
End joinable_top_r.

Definition unit_join : unit -> unit -> unit :=
    fun _ _ => tt.
Hint Unfold unit_join : soundness.

Global Instance unit_joinable : Joinable unit unit.
Proof.
  split with unit_join. destruct x, y; reflexivity.
Defined.

Section identity_joinable.
  Context {A B : Type} `{Joinable A B}.

  Definition identity_join (i j : Identity A) : Identity B :=
    match i, j with
    | identity a, identity a' => identity (a ⊔ a')
    end.

  Global Instance identity_joinable : Joinable (Identity A) (Identity B).
  Proof.
    split with identity_join. destruct x, y; simpl. rewrite join_comm.
    reflexivity.
  Defined.
End identity_joinable.

Section option_joinable.
  Context {A : Type} `{A_joinable : Joinable A A}.

  Definition option_join (m n : option A) : option A :=
    match m, n with
    | Some x, Some y => Some (x ⊔ y)
    | _, _ => None
    end.

  Global Instance option_joinable : Joinable (option A) (option A).
  Proof.
    split with option_join. destruct x, y; simpl. rewrite join_comm.
    all: reflexivity.
  Defined.
End option_joinable.

Section optionA_joinable.
  Context {A : Type} `{A_joinable : Joinable A A}.

  Definition optionA_join
    (st1 st2 : optionA A) : optionA A :=
    match st1, st2 with
    | NoneA, NoneA => NoneA
    | SomeA x, SomeA y => SomeA (x ⊔ y)
    | SomeA x, NoneA | NoneA, SomeA x =>  SomeOrNoneA x
    | NoneA, SomeOrNoneA x | SomeOrNoneA x, NoneA => SomeOrNoneA x
    | SomeA x, SomeOrNoneA y | SomeOrNoneA x, SomeA y => 
        SomeOrNoneA (x ⊔ y)
    | SomeOrNoneA x, SomeOrNoneA y => SomeOrNoneA (x ⊔ y)
    end.
  Hint Unfold optionA_join : soundness.

  Global Instance optionA_joinable : Joinable (optionA A) (optionA A).
  Proof.
    split with optionA_join. destruct x, y; simpl; try rewrite join_comm;
    reflexivity.
  Defined.
End optionA_joinable.

Section joinable_pairs.
  Context {A B A' B'} `{A_joinable : Joinable A A', B_joinable : Joinable B B'}.

  Definition pair_join (p q : (A*B)%type) : (A'*B')%type :=
    ((fst p) ⊔ (fst q), (snd p) ⊔ (snd q)).

  Global Instance joinable_pairs : Joinable (A*B) (A'*B').
  Proof.
    split with pair_join. destruct x, y; simpl. unfold pair_join; simpl.
    rewrite (join_comm a0 a), (join_comm b0 b). reflexivity.
  Defined.
End joinable_pairs.

Section joinable_sums.
    Context {A A' B B'} `{JA : Joinable A A', JB : Joinable B B'}.

    Definition sum_join : (A+B) → (A+B) → (A'+B')+⊤ := 
      λ s1, λ s2, match s1, s2 with
                  | inl x, inl y => NotTop (inl (x ⊔ y))
                  | inr x, inr y => NotTop (inr (x ⊔ y))
                  | _, _ => Top
                  end.

    Global Instance joinable_sums : Joinable (A+B) ((A'+B')+⊤).
    Proof.
      split with sum_join. intros x y. unfold sum_join. destruct x, y; try
      rewrite join_comm; reflexivity.
    Defined.
End joinable_sums.
