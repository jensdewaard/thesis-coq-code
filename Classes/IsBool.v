Require Export Base.
Require Import Classes.Joinable Classes.Galois.

Class and_op (A : Type) : Type := and : A → A → A.
Infix "&&" := and.

Class and_op_sound {A A' : Type} {GA : Galois A A'} 
  (AO : and_op A) (AO' : and_op A') : Prop :=
  and_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 && a2) (a1' && a2').

Instance and_op_bool : and_op bool := andb.

Instance and_top {A : Type} (AO : and_op A) : and_op (A+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | NotTop x, NotTop y => NotTop (x && y)
              | _,_ => Top
              end.

Instance and_top_sound {A A'} {GA : Galois A A'}
  (AO : and_op A) (AO' : and_op A') :
  and_op_sound AO AO' → and_op_sound (and_top AO) AO'.
Proof.
  intro AS. intros a1 a2 a1' a2' Ha Ha'. destruct a1, a2; eauto with soundness.
  apply AS; assumption.
Qed.
Hint Resolve and_top_sound : soundness.

Instance and_bot {A : Type} {AO : and_op A} : and_op (A+⊥) :=
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
Class if_op_sound {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'}
  (IO : if_op A B) (IO' : if_op A' B') : Prop :=
  if_sound : ∀ (g : A) (g' : A') (p1 p2 : B) (p1' p2' : B'),
    γ g g' →
    γ p1 p1' → 
    γ p2 p2' →
    γ (when g p1 p2) (when g' p1' p2').

Instance if_op_bool {B : Type} : if_op bool B := 
  λ (b : bool),
  λ (p1 : B), λ (p2 : B),
  if b then p1 else p2.

Instance if_top {A B : Type} {JB : Joinable B B} (IO : if_op A B) : if_op (A+⊤) B :=
  λ a, λ b1, λ b2, match a with
                   | Top => b1 ⊔ b2
                   | NotTop b => when b b1 b2
                   end.

Instance if_top_sound {A B B'} {GA : Galois A bool} {GB : Galois B B'}
  {JB : Joinable B B} {JBS : JoinableSound JB}
  {IO : if_op A B} :
  if_op_sound IO (if_op_bool (B:=B')) →
  if_op_sound (if_top IO) (if_op_bool (B:=B')).
Proof.
  intros IOS. intros g g' p1 p2 p1' p2' Hg Hp1 Hp2.
  destruct g.
  - (* Top *) unfold when. simpl. destruct g'; simpl. 
    + apply JBS. left. assumption.
    + apply JBS. right. assumption.
  - (* NotTop *) apply IOS; assumption.
Qed.
Hint Resolve if_top_sound : soundness.

Instance if_top_sound' {A B B'} {GA : Galois A bool} {GB : Galois B B'}
  {JB : Joinable B B} {JBS : JoinableSound JB}
  {IO : if_op A B}  :
  if_op_sound IO (if_op_bool (B:=B')) →
  if_op_sound (if_top IO) (if_op_bool (B:=B')).
Proof.
  intros IOS. intros g g' p1 p2 p1' p2' Hg Hp1 Hp2.
  destruct g. 
  - destruct g'; cbn; apply JBS; [left | right]; assumption.
  - apply IOS; assumption.
Qed.

