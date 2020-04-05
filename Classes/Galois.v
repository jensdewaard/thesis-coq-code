Require Export Base.

Class Galois (A A' : Type) : Type :=  γ : A -> ℘ A'.
Arguments γ : simpl never.
Hint Extern 10 (γ _ _) => constructor : soundness.

Ltac gamma_destruct := repeat
  match goal with
  | x : γ _  _ |- _ => inv x
  end.

Definition gamma_bot {A A'} `{Galois A A'} : (A+⊥) → A' → Prop :=
  λ a : A+⊥, match a with
             | Bot => λ _, False
             | NotBot x => λ y, γ x y
             end.

Instance galois_bot {A A'} `{Galois A A'} : Galois (A+⊥) A' := gamma_bot.

Definition gamma_top {A A'} `{Galois A A'} : (A+⊤) → ℘ A' :=
  λ a : A+⊤, match a with
             | Top => λ _, True
             | NotTop x => λ y, γ x y
             end.
Instance galois_top {A A'} `{Galois A A'} : Galois (A+⊤) A' := gamma_top.

Section galois_functions.
  Context {A A' B B' : Type}  
          `{A_galois : Galois A A', B_galois : Galois B B'}.

  Inductive gamma_fun : (A → B) → (A' → B') → Prop :=
    | gamma_fun_cons : ∀ (f : A → B) (g : A' → B'), 
        (∀ (a : A) (a' : A'),
        γ a a' → γ (f a) (g a')) → gamma_fun f g.

  Global Instance galois_fun : Galois (A → B) (A' → B') := gamma_fun.
End galois_functions.
Hint Constructors gamma_fun : soundness.

Section galois_unit.
  Definition gamma_unit (u v : unit) : Prop := True.

  Global Instance galois_unit : Galois unit unit := gamma_unit.
End galois_unit.
Hint Unfold gamma_unit : soundness.

Section galois_pairs.
  Context {A A' B B'} `{A_galois : Galois A A'} `{B_galois : Galois B B'}.

  Inductive gamma_pairs : prod A B → prod A' B' → Prop :=
    | gamma_pairs_cons : ∀ p q,
        γ (fst p) (fst q) → γ (snd p) (snd q) → gamma_pairs p q.

  Global Instance galois_pairs : Galois (A*B)%type (A'*B')%type := gamma_pairs.
End galois_pairs.
Hint Constructors gamma_pairs : soundness.

Section galois_sums.
  Context {A A' B B'} `{GA : Galois A A'} `{GB : Galois B B'}.

  Definition gamma_sum : (A+B) → ℘ (A'+B') := λ s, λ s',
      match s, s' with 
      | inl x, inl y => γ x y
      | inr x, inr y => γ x y
      | _, _ => False
      end.

  Global Instance galois_sum : Galois (A+B) (A'+B') := gamma_sum.
End galois_sums.

Section galois_identity.
  Context {A A'} `{A_galois : Galois A A'}.

  Definition gamma_identity (ia' : Identity A) 
                            (ia : Identity A') : Prop :=
    match ia', ia with
    | identity a', identity a => γ a' a
    end.

  Global Instance galois_identity : Galois (Identity A) (Identity A') :=
    gamma_identity.
End galois_identity.

Section galois_option.
  Context {A A'} `{A_galois : Galois A A'}.

  Inductive gamma_optionA : optionA A → option A' → Prop :=
    | gamma_noneA : gamma_optionA NoneA None
    | gamma_SomeornoneA_none : ∀ a, 
        gamma_optionA (SomeOrNoneA a) None
    | gamma_SomeA_Some : ∀ a' a, γ a' a → gamma_optionA (SomeA a') (Some a)
    | gamma_Someornone_Some : ∀ a' a, 
        γ a' a →
        gamma_optionA (SomeOrNoneA a') (Some a).
  Hint Constructors gamma_optionA : soundness.

  Inductive gamma_option : option A → option A' → Prop :=
    | gamma_none : ∀ m, gamma_option None m
    | gamma_Some_Some : ∀ a' a, γ a' a → gamma_option (Some a') (Some a).
  Hint Constructors gamma_option : soundness.

  Global Instance galois_optionA : Galois (optionA A) (option A') :=
    gamma_optionA.

  Global Instance galois_option : Galois (option A) (option A') :=
    gamma_option.
End galois_option.
Hint Constructors gamma_optionA gamma_option : soundness.

Class SubType_sound (super super' : Type) `{GS : Galois super super'} : Type :=
{
  inject_sound : ∀ {sub sub' : Type} `{ST : SubType sub super}
    `{ST' : SubType sub' super'} `{GS : Galois sub sub'} (s : sub) (s' : sub'),
    γ s s' → γ (inject s) (inject s'); 
  project_sound : ∀ {sub sub' : Type} `{ST : SubType sub super}
    `{ST' : SubType sub' super'} `{GS : Galois sub sub'} (s : super) (s' : super'),
    γ s s' → γ (project s) (project s');
}.
