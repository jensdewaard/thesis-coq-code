Require Export Base.
Require Import Classes.Galois.

Class plus_op (A B : Type) := plus : A → A → B.
Infix "+" := plus.
Class plus_op_sound (A A' : Type) {B B'} `{Galois A A', Galois B B'} 
  `{plus_op A B} `{plus_op A' B'} : Prop :=
  plus_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 + a2) (a1' + a2').

Instance nat_plus_op : plus_op nat nat := Nat.add.

Instance top_plus_op_r {A B : Type} `{plus_op A B} : plus_op A (B+⊤) :=
  λ a1 : A, λ a2 : A, NotTop (a1 + a2).

Instance top_plus_op_l {A B : Type} `{plus_op A (B+⊤)} : plus_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => x + y
              end.

Class mult_op (A B : Type) := mult : A → A → B.
Infix "*" := mult.
Class mult_op_sound (A A' : Type) {B B'} `{Galois A A', Galois B B'}
  `{mult_op A B} `{mult_op A' B'} : Prop :=
  mult_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 * a2) (a1' * a2').

Instance nat_mult_op : mult_op nat nat := Nat.mul.

Instance top_mult_op_r {A B : Type} `{mult_op A B} : mult_op A (B+⊤) :=
  λ a1 : A, λ a2 : A, NotTop (a1 * a2).

Instance top_mult_op_l {A B : Type} `{mult_op A (B+⊤)} : mult_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => x * y
              end.

Class eq_op (A B : Type) := eq : A → A → B.
Infix "=" := eq.
Class eq_op_sound (A A' : Type) {B B'} `{Galois A A', Galois B B'}
  `{eq_op A B} `{eq_op A' B'} : Prop :=
  eq_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 = a2) (a1' = a2').

Instance nat_eq_op : eq_op nat bool := Nat.eqb.

Instance top_eq_op_r {A B : Type} `{eq_op A B} : eq_op A (B+⊤) :=
  λ a1 : A, λ a2 : A, NotTop (a1 = a2).

Instance top_eq_op_l {A B : Type} `{eq_op A (B+⊤)} : eq_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => x = y
              end.

Class leb_op (A B : Type) := leb : A → A → B.
Class leb_op_sound (A A' : Type) {B B'} `{Galois A A', Galois B B'}
  `{leb_op A B} `{leb_op A' B'} : Prop :=
  leb_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' → 
  γ (leb a1 a2) (leb a1' a2').

Instance nat_leb_op : leb_op nat bool := Nat.leb.

Instance top_leb_op_r {A B : Type} `{leb_op A B} : leb_op A (B+⊤) :=
  λ a1, λ a2, NotTop (leb a1 a2).

Instance top_leb_op_l {A B : Type} `{leb_op A (B+⊤)} : leb_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => leb x y
              end.

(*Class IsNat (M : Type -> Type)
  (valType boolType natType : Type) : Type :=
{
  ensure_nat  : valType -> M natType;
  build_nat   : natType -> M valType;
  extract_nat : nat -> M natType;
  plus_op     : natType -> natType -> M natType;
  mult_op     : natType -> natType -> M natType;
  eq_op       : natType -> natType -> M boolType;
  le_op       : natType -> natType -> M boolType;
}.
*)
