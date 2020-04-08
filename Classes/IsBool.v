Require Export Base.
Require Import Classes.Joinable Classes.Galois.

Class and_op (A B : Type) : Type := and : A → A → B.
Infix "&&" := and.

Class and_op_sound {A A' B B' : Type} {GA : Galois A A'} {GB :Galois B B'}
  (AO : and_op A B) (AO' : and_op A' B') : Prop :=
  and_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 && a2) (a1' && a2').

Instance and_op_bool : and_op bool bool := andb.

Instance and_top {A B : Type} (AO : and_op A B) : and_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | NotTop x, NotTop y => NotTop (x && y)
              | _,_ => Top
              end.

Instance and_top_sound {A A' B B'} {GA : Galois A A'} {GB : Galois B B'}
  (AO : and_op A B) (AO' : and_op A' B') :
  and_op_sound AO AO' → and_op_sound (and_top AO) AO'.
Proof.
  intro AS. intros a1 a2 a1' a2' Ha Ha'. destruct a1, a2; eauto with soundness.
  apply AS; assumption.
Qed.
Hint Resolve and_top_sound : soundness.

Instance and_bot {A B : Type} `{and_op A B} : and_op (A+⊥) (B+⊥) :=
  λ a1, λ a2, match a1, a2 with
              | NotBot x, NotBot y => NotBot (x && y)
              | _, _ => Bot
              end.

Class or_op  (A B : Type) : Type := or : A → A → B.
Infix "||" := or.
Class or_op_sound (A A' : Type) {B B' : Type} `{Galois A A', Galois B B'}
  `{or_op A B} `{or_op A' B'} : Prop :=
  or_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 || a2) (a1' || a2').

Instance or_op_bool : or_op bool bool := orb.

Instance or_top {A B : Type} `{or_op A B} : or_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | NotTop x, NotTop y => NotTop (x || y)
              | _, _ => Top
              end.

Instance or_bot {A B : Type} `{or_op A B} : or_op (A+⊥) (B+⊥) :=
  λ a1, λ a2, match a1, a2 with
              | NotBot x, NotBot y => NotBot (x || y)
              | _, _ => Bot
              end.

Class neg_op (A B : Type) : Type := neg : A → B.
Class neg_op_sound {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'}
  (NO : neg_op A B) (NO' : neg_op A' B') : Prop :=
  neg_sound : ∀ (a : A) (a' : A'),
  γ a a' →
  γ (neg a) (neg a').

Instance neg_op_bool : neg_op bool bool := negb.

Instance neg_top {A B : Type} (NO : neg_op A B) : neg_op (A+⊤) (B+⊤) :=
  λ a, match a with | NotTop x => NotTop (neg x) | Top => Top end.

Instance neg_top_sound {A A' B B'} {GA : Galois A A'} {GB : Galois B B'}
  (NO : neg_op A B) (NO' : neg_op A' B') :
  neg_op_sound NO NO' → neg_op_sound (neg_top NO) NO'.
Proof.
  intro NS. intros a a' Ha. destruct a.
  - constructor. 
  - apply NS. apply Ha.
Qed.
Hint Resolve neg_top_sound : soundness.

Instance neg_bot {A B : Type} `{neg_op A B} : neg_op (A+⊥) (B+⊥) :=
  λ a, match a with | NotBot x => NotBot (neg x) | Bot => Bot end.

Class if_op  (A B : Type) : Type := when : A → B → B → B.
Class if_op_sound (A A' : Type) {B B' : Type} `{Galois A A', Galois B B'}
  `{if_op A B} `{if_op A' B'} : Prop :=
  if_sound : ∀ (g : A) (g' : A') (p1 p2 : B) (p1' p2' : B'),
    γ g g' →
    γ p1 p1' → 
    γ p2 p2' →
    γ (when g p1 p2) (when g' p1' p2').

Instance if_op_bool {B : Type} : if_op bool B := 
  λ (b : bool),
  λ (p1 : B), λ (p2 : B),
  if b then p1 else p2.

Instance if_top {A B : Type} `{if_op A B} `{Joinable B B} : if_op (A+⊤) B :=
  λ a, λ b1, λ b2, match a with
                   | Top => b1 ⊔ b2
                   | NotTop b => when b b1 b2
                   end.

(*Class IsBool (M : Type -> Type) (valType boolType : Type) : Type :=
{
  ensure_bool  : valType -> M boolType;
  build_bool   : boolType -> M valType;
  extract_bool : bool -> M boolType;
  and_op       : boolType -> boolType -> M boolType;
  neg_op       : boolType -> M boolType;
  if_op        : boolType -> M unit -> M unit -> M unit;
}.*)
