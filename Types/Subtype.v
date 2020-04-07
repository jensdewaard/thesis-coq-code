Require Export Base.
Require Import Classes.Galois.

Class SubType (sub : Type) (super : Type) : Type := {
  inject : sub → super;
  project : super → option sub
}.

Class SubType_sound (super super' : Type) `{GS : Galois super super'} : Type :=
{
  inject_sound : ∀ {sub sub' : Type} {ST : SubType sub super}
    {ST' : SubType sub' super'} {GS : Galois sub sub'} (s : sub) (s' : sub'),
    γ s s' → γ (inject s) (inject s'); 
  project_sound : ∀ {sub sub' : Type} {ST : SubType sub super}
    {ST' : SubType sub' super'} {GS : Galois sub sub'} (s : super) (s' : super'),
    γ s s' → γ (project s) (project s');
}.

Instance subtype_l : ∀ {A B}, SubType A (A + B) := {
  inject := inl;
  project := λ s, match s with | inl x => Some x | _ => None end
}.

Instance subtype_r : ∀ {A B}, SubType B (A+B) := {
  inject := inr;
  project := λ s, match s with | inr x => Some x | _ => None end
}.

Instance subtype_trans_r : ∀ {A B C} `{SubType A B}, SubType A (C + B) := {
  inject := inject ∘ inr;
  project := λ s, match s with | inr x => project x | _ => None end
}.

Instance subtype_trans_l {A B C} `{S : SubType A B} : SubType A (B + C).
Proof. destruct S as [inject project]. split.
  - exact (λ a, inl (inject a)).
  - exact (λ bc, match bc with
                 | inr _ => None
                 | inl b => project b
                 end).
Defined.

Instance subtype_top_r : ∀ A, SubType A (A+⊤) := {
  inject := NotTop;
  project := λ a, match a with
                  | Top => None
                  | NotTop x => Some x
                  end;
}.

Instance subtype_bot_r : ∀ A, SubType A (A+⊥) := {
  inject := NotBot;
  project := λ a, match a with
                  | Bot => None
                  | NotBot x => Some x
                  end;
}.

Instance subtype_top_l {A B} `{SubType A B} : 
  SubType (A+⊤) (B+⊤).
Proof. destruct H as [inject project]. split.
  exact (λ a : (A+⊤), match a with
                      | Top => Top
                      | NotTop x => NotTop( inject x)
                      end).
  exact (λ b : (B+⊤), match b with
                      | Top => None
                      | NotTop x => match (project x) with
                                    | Some x' => Some (NotTop x')
                                    | None => None
                                    end
                      end).
Defined.
