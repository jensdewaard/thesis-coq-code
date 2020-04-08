Require Export Base.
Require Import Classes.Galois.

Class plus_op (A B : Type) := plus : A → A → B.
Infix "+" := plus.
Class plus_op_sound {A A' : Type} {B B' : Type} 
  {GA : Galois A A'} {GB : Galois B B'} 
  (PO : plus_op A B) (PO' : plus_op A' B') : Prop :=
  plus_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 + a2) (a1' + a2').

Instance nat_plus_op : plus_op nat nat := Nat.add.

Instance top_plus_op_r {A B : Type} (PO : plus_op A B) : plus_op A (B+⊤) :=
  λ a1 : A, λ a2 : A, NotTop (a1 + a2).

Instance top_plus_op_r_sound {A A' B B' : Type}
  {PO : plus_op A B} {PO' : plus_op A' B'}
  {GA : Galois A A'} {GB : Galois B B'} :
  plus_op_sound PO PO' → plus_op_sound (top_plus_op_r PO) PO'.
Proof.
  intro PS. intros a1 a2 a1' a2' Ha Ha'. unfold plus. unfold top_plus_op_r.
  unfold γ; simpl. apply PS; assumption.
Qed.
Hint Resolve top_plus_op_r_sound : soundness.

Instance top_plus_op_l {A B : Type} (PO : plus_op A (B+⊤)) : plus_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => x + y
              end.

Instance top_plus_op_l_sound {A A' B B' : Type} 
  {PO : plus_op A (B+⊤)} {PO' : plus_op A' B'} 
  {GA : Galois A A'} {GB : Galois B B'} :
  plus_op_sound PO PO' → plus_op_sound (top_plus_op_l PO) PO'.
Proof.
  intro PS. intros a1 a2 a1' a2' Ha Ha'; destruct a1, a2;
  eauto with soundness. 
Qed.
Hint Resolve top_plus_op_l_sound : soundness.

Class mult_op (A B : Type) := mult : A → A → B.
Infix "*" := mult.
Class mult_op_sound {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'}
  (MO : mult_op A B) (MO' : mult_op A' B') : Prop :=
  mult_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 * a2) (a1' * a2').

Instance nat_mult_op : mult_op nat nat := Nat.mul.

Instance top_mult_op_r {A B : Type} (MO : mult_op A B) : mult_op A (B+⊤) :=
  λ a1 : A, λ a2 : A, NotTop (a1 * a2).

Instance top_mult_op_r_sound {A A' B B' : Type}
  {GA : Galois A A'} {GB : Galois B B'}
  {MO : mult_op A B} {MO' : mult_op A' B'} :
  mult_op_sound MO MO' → mult_op_sound (top_mult_op_r MO) MO'.
Proof.
  intro MS. intros a1 a2 a1' a2' Ha Ha'. unfold mult. unfold top_mult_op_r.
  unfold γ; simpl. apply MS; assumption.
Qed.
Hint Resolve top_mult_op_r_sound : soundness.

Instance top_mult_op_l {A B : Type} (MO : mult_op A (B+⊤)) : mult_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => x * y
              end.

Instance top_mult_op_l_sound {A A' B B'} {GA : Galois A A'} {GB : Galois B B'}
  (MO : mult_op A (B+⊤)) (MO' : mult_op A' B') :
  mult_op_sound MO MO' → mult_op_sound (top_mult_op_l MO) MO'.
Proof.
  intro MS. intros a1 a1' a2 a2' Ha Ha'. destruct a1, a1';
  eauto with soundness.
Qed.
Hint Resolve top_mult_op_l_sound : soundness.

Class eq_op (A B : Type) := eq : A → A → B.
Infix "=" := eq.
Class eq_op_sound {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'}
  (EO : eq_op A B) (EO' : eq_op A' B') : Prop :=
  eq_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' →
  γ (a1 = a2) (a1' = a2').

Instance nat_eq_op : eq_op nat bool := Nat.eqb.

Instance top_eq_op_r {A B : Type} (EO : eq_op A B) : eq_op A (B+⊤) :=
  λ a1 : A, λ a2 : A, NotTop (a1 = a2).

Instance top_eq_op_r_sound {A A' B B'} {GA : Galois A A'} {GB : Galois B B'}
  (EO : eq_op A B) (EO' : eq_op A' B') :
  eq_op_sound EO EO' → eq_op_sound (top_eq_op_r EO) EO'.
Proof.
  intro ES. intros a1 a2 a1' a2' Ha Ha'. unfold eq, top_eq_op_r.
  unfold γ; simpl. eauto with soundness. 
Qed.
Hint Resolve top_eq_op_r_sound : soundness.

Instance top_eq_op_l {A B : Type} (EO : eq_op A (B+⊤)) : eq_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => x = y
              end.

Instance top_eq_op_l_sound {A A' B B'} {GA : Galois A A'} {GB : Galois B B'}
  (EO : eq_op A (B+⊤)) (EO' : eq_op A' B') :
  eq_op_sound EO EO' → eq_op_sound (top_eq_op_l EO) EO'.
Proof.
  intro ES. intros a1 a2 a1' a2' Ha Ha'. destruct a1; simpl.
  - reflexivity.
  - destruct a2; try reflexivity. apply ES; assumption.
Qed.
Hint Resolve top_eq_op_l_sound : soundness.

Class leb_op (A B : Type) := leb : A → A → B.
Class leb_op_sound {A A' B B'} `{Galois A A', Galois B B'}
  (LO : leb_op A B) (LO' : leb_op A' B') : Prop :=
  leb_sound : ∀ (a1 a2 : A) (a1' a2' : A'),
  γ a1 a1' →
  γ a2 a2' → 
  γ (leb a1 a2) (leb a1' a2').

Instance nat_leb_op : leb_op nat bool := Nat.leb.

Instance top_leb_op_r {A B : Type} (LO : leb_op A B) : leb_op A (B+⊤) :=
  λ a1, λ a2, NotTop (leb a1 a2).

Instance top_leb_op_r_sound {A A' B B'} {GA : Galois A A'} {GB : Galois B B'}
  (LO : leb_op A B) (LO' : leb_op A' B') : 
  leb_op_sound LO LO' → leb_op_sound (top_leb_op_r LO) LO'.
Proof.
  intro LS. intros a1 a2 a1' a2' Ha Ha'. unfold leb, top_leb_op_r.
  unfold γ;simpl. apply LS; assumption.
Qed.
Hint Resolve top_leb_op_r_sound : soundness.

Instance top_leb_op_l {A B : Type} (LO : leb_op A (B+⊤)) : leb_op (A+⊤) (B+⊤) :=
  λ a1, λ a2, match a1, a2 with
              | Top, _ | _, Top => Top
              | NotTop x, NotTop y => leb x y
              end.

Instance top_leb_op_l_sound {A A' B B'} {GA : Galois A A'} {GB : Galois B B'}
  (LO : leb_op A (B+⊤)) (LO' : leb_op A' B') :
  leb_op_sound LO LO' → leb_op_sound (top_leb_op_l LO) LO'.
Proof.
  intro LS. intros a1 a2 a1' a2' Ha Ha'. destruct a1, a2; simpl; eauto with
    soundness.
Qed.
Hint Resolve top_leb_op_l_sound : soundness.
