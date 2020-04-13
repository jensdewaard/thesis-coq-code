Require Export Base.

Class Galois (A A' : Type) : Type :=  γ : A -> ℘ A'.
Arguments γ : simpl never.
Hint Extern 10 (γ _ _) => constructor : soundness.

Ltac gamma_destruct := repeat
  match goal with
  | x : γ _  _ |- _ => inv x
  end.

Definition gamma_bot (A A' : Type) `{Galois A A'} : (A+⊥) → A' → Prop :=
  λ a : A+⊥, match a with
             | Bot => λ _, False
             | NotBot x => λ y, γ x y
             end.


Instance galois_bot : ∀ (A A' : Type),
  Galois A A' → Galois (A+⊥) A' := gamma_bot.

Definition gamma_top (A A' : Type) `{Galois A A'} : (A+⊤) → ℘ A' :=
  λ a : A+⊤, match a with
             | Top => λ _, True
             | NotTop x => λ y, γ x y
             end.
Instance galois_top : ∀  (A A' : Type), Galois A A' → Galois (A+⊤) A' := 
  gamma_top.

Definition gamma_fun {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'} 
  : (A → B) → (A' → B') → Prop := λ (f : A → B), λ (g : A' → B'),
    ∀ (a : A) (a' : A'), γ a a' → γ (f a) (g a').
Arguments gamma_fun A A' {B B'} {GA GB}.

Instance galois_fun : ∀ (A A' : Type) {B B' : Type},
  Galois A A' →
  Galois B B' →
  Galois (A → B) (A' → B') := gamma_fun.

Instance galois_unit : Galois unit unit := λ _, λ _, True.

Inductive gamma_pairs {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'} 
: prod A B → prod A' B' → Prop :=
    | gamma_pairs_cons : ∀ p q,
        γ (fst p) (fst q) → γ (snd p) (snd q) → gamma_pairs p q.
Arguments gamma_pairs A A' B B' {GA GB}.

Global Instance galois_pairs : ∀ A A' B B' : Type,
Galois A A' →
Galois B B' →
Galois (A*B)%type (A'*B')%type := gamma_pairs.

Lemma fst_sound : ∀ (A A' : Type) {GA : Galois A A'} {B B' : Type} {GB : Galois B B'} 
  (p : A*B) (q : A'*B'),
  γ p q → 
  γ (fst p) (fst q).
Proof.
  intros. destruct p eqn:Hp, q eqn:Hq; simpl. inversion H. subst.
  simpl in *. assumption.
Qed.

Corollary snd_sound : ∀ (A A' : Type) {GA : Galois A A'} {B B' : Type} {GB : Galois B B'} 
  (p : A*B) (q : A'*B'),
  γ p q → 
  γ (snd p) (snd q).
Proof.
  intros. destruct p, q; simpl. inversion H. subst. simpl in *. assumption.
Qed.

Definition gamma_sum {A A' B B'} {GA : Galois A A'} {GB : Galois B B'} : 
    (A+B) → ℘ (A'+B') := λ s, λ s',
      match s, s' with 
      | inl x, inl y => γ x y
      | inr x, inr y => γ x y
      | _, _ => False
      end.
Arguments gamma_sum A A' B B' {GA GB}.

Instance galois_sum : ∀ (A A' B B' : Type),
  Galois A A' →
  Galois B B' →
  Galois (A+B) (A'+B') := gamma_sum.

Definition gamma_identity {A A'} {GA : Galois A A'} (ia : Identity A) 
                            (ia' : Identity A') : Prop :=
    match ia, ia' with
    | identity a, identity a' => γ a a'
    end.
Arguments gamma_identity A A' {GA} ia ia'.

Instance galois_identity : ∀ (A A' : Type),
  Galois A A' →
  Galois (Identity A) (Identity A') :=
    gamma_identity.

Inductive gamma_optionA {A A'} {GA : Galois A A'} : optionA A → option A' → Prop :=
  | gamma_noneA : gamma_optionA NoneA None
  | gamma_SomeornoneA_none : ∀ a, 
      gamma_optionA (SomeOrNoneA a) None
  | gamma_SomeA_Some : ∀ a' a, γ a' a → gamma_optionA (SomeA a') (Some a)
  | gamma_Someornone_Some : ∀ a' a, 
      γ a' a →
      gamma_optionA (SomeOrNoneA a') (Some a).

Inductive gamma_option {A A'} {GA : Galois A A'} : option A → option A' → Prop :=
  | gamma_none : ∀ m, gamma_option None m
  | gamma_Some_Some : ∀ a' a, γ a' a → gamma_option (Some a') (Some a).

Instance galois_optionA : ∀ A A' (GA : Galois A A'), 
  Galois (optionA A) (option A') := @gamma_optionA.

Instance galois_option : ∀ A A' (GA : Galois A A'), 
  Galois (option A) (option A') := @gamma_option.

Instance galois_optionAT {M M'} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : 
    ∀ A A', 
  Galois A A' → Galois (optionAT M A) (optionT M' A').
Proof.
  intros A A' GA. apply GM. apply galois_optionA. apply GA.
Defined.

Instance galois_optionT {M M'} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} :
  ∀ A A', Galois A A' → Galois (optionT M A) (optionT M' A').
Proof.
  intros A A' GA. apply GM. apply galois_option. apply GA.
Defined.

Class extract_op (A B : Type) : Type := extract : A → B.

Class extract_op_sound {A B B' : Type} {GB : Galois B B'}
  (EO : extract_op A B) (EO' : extract_op A B') : Prop :=
  extract_sound :  ∀ a, γ (extract a) (extract a).

Instance extract_nat : extract_op nat nat := id.
Instance extract_bool : extract_op bool bool := id.

Instance extract_sum {A B C D : Type} 
  (EA : extract_op A C) (EB : extract_op B D) : extract_op (A+B) (C+D) :=
    λ v, 
      match v with
      | inl x => inl (extract x)
      | inr x => inr (extract x)
      end.

Instance extract_sum_sound {A B C C' D D'} 
  {GC : Galois C C'} {GD : Galois D D'}
  {EA : extract_op A C} {EA' : extract_op A C'}
  {EB : extract_op B D} {EB' : extract_op B D'}
  {EAS : extract_op_sound EA EA'} {EBS : extract_op_sound EB EB'} :
  extract_op_sound (extract_sum EA EB) (extract_sum EA' EB').
Proof.
  intro p; destruct p; apply EAS + apply EBS.
Qed.
         
Instance extract_top {A B : Type}
  (EA : extract_op A B) : extract_op A (B+⊤) := λ a, NotTop (extract a).

Instance extract_top_sound {A B B'} {GB : Galois B B'}
  {EA : extract_op A B} {EA' : extract_op A B'} 
  {EAS : extract_op_sound EA EA'} : 
  extract_op_sound (extract_top EA) EA'.
Proof. apply EAS. Qed.


