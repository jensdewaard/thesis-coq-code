Require Export Base.
Require Import Classes.Galois.

Class Joinable (A B : Type) : Type := join_op : A → A → B.
Arguments join_op : simpl never.
Infix "⊔" := join_op (at level 40).

Class JoinableSound (A B C : Type) 
  `{Joinable A B} `{Galois A C} `{Galois B C} : Prop :=
  join_sound : ∀ x y : A, γ x ∪ γ y ⊆ γ (x ⊔ y).

Instance functions_joinable {A B} `{Joinable B B} : 
Joinable (A → B) (A → B) := λ f, λ g, λ a : A, (f a) ⊔ (g a).

Instance top_joinable_l {A} `{Joinable A (A+⊤)} : Joinable (A+⊤) (A+⊤) :=
  λ a, λ a', 
    match a, a' with
    | NotTop x, NotTop y => x ⊔ y
    | _, _ => Top
    end.

Instance top_joinable_r {A} `{Joinable A A} : Joinable A (A+⊤) :=
  λ a : A, λ a' : A, NotTop (a ⊔ a').

Instance unit_joinable : Joinable unit unit := λ _, λ _,  tt.

Instance identity_joinable {A B} `{Joinable A B} : Joinable (Identity A) (Identity B) :=
  λ i, λ j,
    match i, j with
    | identity a, identity a' => identity (a ⊔ a')
    end.

Instance option_joinable {A B} `{Joinable A B} : Joinable (option A) (option B) :=
  λ m, λ n,
    match m, n with
    | Some x, Some y => Some (x ⊔ y)
    | _, _ => None
    end.

Instance optionA_joinable {A} `{Joinable A A} : Joinable (optionA A) (optionA A) :=
  λ m, λ n,
    match m, n with
    | NoneA, NoneA => NoneA
    | SomeA x, SomeA y => SomeA (x ⊔ y)
    | SomeA x, NoneA | NoneA, SomeA x =>  SomeOrNoneA x
    | NoneA, SomeOrNoneA x | SomeOrNoneA x, NoneA => SomeOrNoneA x
    | SomeA x, SomeOrNoneA y | SomeOrNoneA x, SomeA y => 
        SomeOrNoneA (x ⊔ y)
    | SomeOrNoneA x, SomeOrNoneA y => SomeOrNoneA (x ⊔ y)
    end.

Instance pair_joinable {A B A' B'} `{Joinable A B, Joinable A' B'} :
  Joinable (A*A')%type (B*B')%type :=
  λ p, λ q, ((fst p) ⊔ (fst q), (snd p) ⊔ (snd q)).

Instance sum_joinable {A B A' B'} `{Joinable A B, Joinable A' B'} :
  Joinable (A+A') ((B+B')+⊤) :=
  λ s1, λ s2,
    match s1, s2 with
    | inl x, inl y => NotTop (inl (x ⊔ y))
    | inr x, inr y => NotTop (inr (x ⊔ y))
    | _, _ => Top
    end.
