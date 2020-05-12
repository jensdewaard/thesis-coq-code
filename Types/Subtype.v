Require Export Base.
Require Import Classes.Galois.
Require Import Types.Option.

Class SubType (sub : Type) (super : Type) : Type := {
  inject : sub → super;
  project : super → option sub
}.

Instance galois_subtype_l : ∀ A B B',
  Galois B B' → Galois (A+B) B'.
Proof. 
  intros A B B' GB. unfold Galois in *.
  exact (λ v : (A+B), 
    match v with
    | inl a => λ _, False
    | inr b => λ b', GB b b'
    end).
Defined.

Class SubType_sound {super super' sub sub' : Type} {Gsuper : Galois super super'} 
  {Gsub : Galois sub sub'} 
  (ST : SubType sub super) (ST' : SubType sub' super') : Type :=
{
  inject_sound : ∀ (s : sub) (s' : sub'),
    γ s s' → γ (inject s) (inject s'); 
  project_sound : ∀ (s : super) (s' : super'),
    γ s s' → γ (project s) (project s');
}.
Hint Resolve inject_sound project_sound : soundness.

Instance subtype_l : ∀ A B, SubType A (A + B) := {
  inject := inl;
  project := λ s, match s with | inl x => Some x | _ => None end
}.

Instance subtype_sound_l : ∀ {A B A' B' : Type} 
  {GA : Galois A A'} {GB : Galois B B'},
  SubType_sound (subtype_l A B) (subtype_l A' B').
Proof.
  intros. split.
  - intros. apply H. 
  - intros. destruct s, s'; simpl; eauto with soundness.
Qed.
Hint Resolve subtype_sound_l : soundness.

Instance subtype_r : ∀ A B, SubType B (A+B) := {
  inject := inr;
  project := λ s, match s with | inr x => Some x | _ => None end
}.

Instance subtype_sound_r : ∀ {A B A' B' : Type}
  {GA : Galois A A'} {GB : Galois B B'},
  SubType_sound (subtype_r A B) (subtype_r A' B').
Proof. split; intros.
  - apply H.
  - destruct s, s'; eauto with soundness; constructor. 
    apply H.
Qed.
Hint Resolve subtype_sound_r : soundness.

Instance subtype_trans_r : ∀ {A B} C, 
  SubType A B → SubType A (C + B) := {
  inject := inject ∘ inr;
  project := λ s, match s with | inr x => project x | _ => None end
}.

Instance subtype_sound_trans_r : ∀ {A A' B B' C}
  {GA : Galois A A'} {GB : Galois B B'}
  (ST : SubType A B) (ST' : SubType A' B'),
  SubType_sound ST ST' →
  SubType_sound (subtype_trans_r C ST) (ST').
Proof.
  Set Printing Implicit.
  intros A A' B B' C GA GB ST ST' SS. split; intros s s' Hs.
  - unfold inject; simpl. unfold compose. unfold γ. 
    simpl.
    unfold galois_subtype_l.
    simpl. apply SS. assumption.
  - destruct s.
    + constructor.
    + simpl. apply SS. apply Hs.
Qed.
Hint Resolve subtype_sound_trans_r : soundness.

Instance subtype_trans_l : ∀ A B C,
  SubType A B → SubType A (B + C) :=
{
  inject := λ a, inl (inject a);
  project := λ bc, match bc with
                   | inr _ => None
                   | inl b => project b
                   end;
}.

Instance subtype_sound_trans_l : ∀ {A A' B B' C C'}
  {GA : Galois A A'} {GB : Galois B B'} {GC : Galois C C'}
  (ST : SubType A B) (ST' : SubType A' B'),
  SubType_sound ST ST' →
  SubType_sound (subtype_trans_l A B C ST) (subtype_trans_l A' B' C' ST').
Proof. split; intros.
  - unfold inject; simpl. unfold γ; simpl. apply inject_sound. assumption.
  - unfold project; simpl. destruct s, s'; eauto with soundness. 
Qed.
Hint Resolve subtype_sound_trans_l : soundness.

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

Instance subtype_top_l : ∀ A B : Type,
  SubType A B → 
  SubType (A+⊤) (B+⊤) := {
  inject := λ a, match a with
                 | Top => Top
                 | NotTop x => NotTop (inject x)
                 end;
  project := λ b, match b with
                  | Top => None
                  | NotTop x => match (project x) with
                                | Some x' => Some (NotTop x')
                                | None => None
                                end
                  end;
}.

Instance subtype_sound_top_l {A A' B B' : Type} {ST : SubType A B}
  {ST' : SubType A' B'} {GA : Galois A A'} {GB : Galois B B'} :
  SubType_sound ST ST' → SubType_sound (subtype_top_l A B ST) ST'.
Proof. split.
  - intros s s' Hs. destruct s.
    + constructor.
    + unfold γ; simpl. apply inject_sound. assumption.
  - intros s s' Hs. destruct s.
    + constructor.
    + cbn. unfold γ in Hs. simpl in Hs. apply project_sound in Hs.
      destruct (project b), (project s'); eauto with soundness.
Qed.
Hint Resolve subtype_sound_top_l : soundness.
