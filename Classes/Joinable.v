Require Export Base.
Require Import Classes.Galois.

Class Joinable (A B : Type) : Type := join_op : A → A → B.

Arguments join_op : simpl never.
Infix "⊔" := join_op (at level 40).

Class JoinableIdem {A} (J : Joinable A A) : Prop :=
  joinable_idem : ∀ a : A, a ⊔ a = a.

Class JoinableSound {A B A' : Type} {GA : Galois A A'} {GB : Galois B A'}
  (JA : Joinable A B)  : Prop :=
  join_sound : ∀ x y : A, γ x ∪ γ y ⊆ γ (x ⊔ y).

Instance functions_joinable {A B C} {JB : Joinable B C} : 
Joinable (A → B) (A → C) := λ f, λ g, λ a : A, (f a) ⊔ (g a).

Instance functions_joinable_idem {A} {JA : Joinable A A} :
  JoinableIdem JA → JoinableIdem (functions_joinable (A:=A)).
Proof.
  intros JAI a. unfold join_op, functions_joinable. ext.
  rewrite JAI. reflexivity.
Qed.

Instance functions_joinable_sound {A A' B' B C} {JB : Joinable B C}
  {GA : Galois A A'} {GB : Galois B B'} {GC : Galois C B'} :
  JoinableSound JB →
  JoinableSound (functions_joinable (A:=A) (B:=B) (C:=C)).
Proof.
  Set Printing Implicit.
  intro JS. intros f g f' [Hf | Hf] a a' Ha; apply JS; [left | right]; auto.
Qed.
Hint Resolve functions_joinable_sound : soundness.

Instance top_joinable_r {A B} (JA : Joinable A B) : Joinable A (B+⊤) :=
  λ a : A, λ a' : A, NotTop (a ⊔ a').

Instance top_joinable_r_sound {A A' B} {JA : Joinable A B} 
  {GA : Galois A A'} {GB : Galois B A'}: 
  JoinableSound JA → 
  JoinableSound (top_joinable_r JA).
Proof.
  intros JS a1 a2 a' Hgamma. unfold γ, galois_top, gamma_top.
  apply JS in Hgamma. unfold "⊔", top_joinable_r. 
  assumption.
Qed.

Instance top_joinable_l {A B} (JA : Joinable A (B+⊤)) : Joinable (A+⊤) (B+⊤) :=
  λ a, λ a', 
    match a, a' with
    | NotTop x, NotTop y => x ⊔ y
    | _, _ => Top
    end.

Instance top_joinable_l_sound {A A' B} {JA : Joinable A (B+⊤)} 
  {GA : Galois A A'} {GB : Galois B A'} :
  JoinableSound JA →
  JoinableSound (top_joinable_l JA).
Proof.
  intros JS a1 a2 a' Hgamma. 
  destruct a1, a2; try constructor. apply JS in Hgamma. apply Hgamma.
Qed.

Instance unit_joinable : Joinable unit unit := λ _, λ _,  tt.

Instance unit_joinable_idem : JoinableIdem unit_joinable.
Proof.
  intro. destruct a; reflexivity.
Qed.

Instance unit_joinable_sound : JoinableSound unit_joinable.
Proof.
  constructor.
Qed.

Instance identity_joinable {A B} `{Joinable A B} : Joinable (Identity A) (Identity B) :=
  λ i, λ j,
    match i, j with
    | identity a, identity a' => identity (a ⊔ a')
    end.

Instance identity_joinable_idem {A} {JA : Joinable A A} :
  JoinableIdem JA → JoinableIdem (@identity_joinable A A JA).
Proof.
  intros JAI a. destruct a. cbv. rewrite JAI. reflexivity.
Qed.

Instance option_joinable {A B} {JA : Joinable A B} : Joinable (option A) (option B) :=
  λ m, λ n,
    match m, n with
    | Some x, Some y => Some (x ⊔ y)
    | _, _ => None
    end.

Instance option_joinable_sound {A A' B} {GA : Galois A A'} {GB : Galois B A'}
  {JA : Joinable A B} :
  JoinableSound JA → 
  JoinableSound option_joinable.
Proof.
  intros JAS.
  intros a a'. unfold γ, galois_option. destruct a, a'; cbv; intros m H; 
  try constructor. destruct H.
  - destruct m. 
     + constructor. inversion H; subst. apply join_sound. left. assumption.
     + inversion H.
  - destruct m.
    + constructor. inversion H; subst. apply join_sound. right. assumption.
    + inversion H.
Qed.
Hint Resolve option_joinable_sound : soundness.

Instance option_joinable_idem {A} {JA : Joinable A A} :
  JoinableIdem JA → JoinableIdem (@option_joinable A A JA).
Proof.
  intros JAI a. destruct a; cbv. rewrite JAI. all: reflexivity.
Qed.
Hint Resolve option_joinable_idem : soundness.

Instance optionT_joinable {M : Type → Type} 
  {JM : ∀ A B, Joinable A B → Joinable (M A) (M B)}
  {A B} {JA : Joinable A B} : Joinable (optionT M A) (optionT M B).
Proof.
  intros m m'. unfold optionT. pose proof option_joinable as JO. 
  apply JM in JO. exact (JO m m').
Defined.

Instance optionA_joinable {A} (JA : Joinable A A) : Joinable (optionA A) (optionA A) :=
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

Instance optionA_joinable_idem {A} {JA : Joinable A A} : 
  JoinableIdem JA → JoinableIdem (@optionA_joinable A JA).
Proof.
  intros JAI.
  intro. destruct a; cbv; try rewrite JAI; reflexivity.
Qed.

Instance optionA_joinable_sound {A A'} {JA : Joinable A A} 
  {GA : Galois A A'} :
  JoinableSound JA → JoinableSound (optionA_joinable JA).
Proof.
  intros JAS a1 a2 a' Hgamma. destruct a1, a2, a'; try constructor; cbn; 
    try apply JAS; inversion Hgamma as [Hg|Hg]; inversion Hg; subst;
        auto. 1,3,5,7: left; auto. all: right; auto.
Qed.
  
Instance optionAT_joinable {M : Type → Type}
  {JM : ∀ A B, Joinable A B → Joinable (M A) (M B)}
  {A} {JA : Joinable A A} : Joinable (optionAT M A) (optionAT M A).
Proof.
  intros m m'. unfold optionT. pose proof (optionA_joinable JA) as JO.
  apply JM in JO. exact (JO m m').
Defined.


Instance pair_joinable {A B C D} {JA : Joinable A C} {JB : Joinable B D} :
  Joinable (A*B)%type (C*D)%type :=
  λ p, λ q, ((fst p) ⊔ (fst q), (snd p) ⊔ (snd q)).

Instance pair_joinable_idem {A A'} {JA : Joinable A A} {JA' : Joinable A' A'} :
  JoinableIdem JA → 
  JoinableIdem JA' → 
  JoinableIdem (@pair_joinable A A' A A' JA JA').
Proof.
  intros JAI JAI' p. destruct p; cbv.  rewrite JAI, JAI'. reflexivity.
Qed.

Instance pair_joinable_sound {A B C D A' B'} 
  {JA : Joinable A C} {JB: Joinable B D}
  {GA : Galois A A'} {GC : Galois C A'}
  {GB : Galois B B'} {GD : Galois D B'} :
  JoinableSound JA →
  JoinableSound JB →
  JoinableSound (@pair_joinable A B C D JA JB).
Proof.
  intros JAS JBS p q p' Hgamma. destruct p, q, p'; simpl.
  constructor; simpl; [apply JAS | apply JBS].
  all: inversion Hgamma; [left | right]; inversion H; subst; assumption.
Qed. 
Hint Resolve pair_joinable_sound : soundness.

Instance sum_joinable {A B C D} (JA : Joinable A C) (JB : Joinable B D) :
  Joinable (A+B) ((C+D)+⊤) :=
  λ s1, λ s2,
    match s1, s2 with
    | inl x, inl y => NotTop (inl (x ⊔ y))
    | inr x, inr y => NotTop (inr (x ⊔ y))
    | _, _ => Top
    end.

Instance sum_joinable_idem {A A'} {JA : Joinable A A} {JA' : Joinable A' A'} :
  JoinableIdem JA →
  JoinableIdem JA' →
  JoinableIdem (@top_joinable_l (A+A') (A+A') (sum_joinable JA JA')).
Proof.
  intros JAI JAI' a. destruct a.
  - constructor.
  - unfold join_op. unfold top_joinable_l. destruct s.
    + unfold join_op. unfold sum_joinable. rewrite JAI. reflexivity.
    + unfold join_op. unfold sum_joinable. rewrite JAI'. reflexivity.
Qed.

Instance sum_joinable_sound {A A' B B' C D} 
  {JA : Joinable A C} {JB : Joinable B D}
  {GA : Galois A A'} {GB : Galois B B'}
  {GC : Galois C A'} {GD : Galois D B'} :
  JoinableSound JA →
  JoinableSound JB →
  JoinableSound (sum_joinable JA JB).
Proof.
  intros JAS JBS.
  intros s1 s2 s' Hgamma. destruct s1, s2, s'; cbv in *; auto; inversion
  Hgamma as [contra | contra]; inversion contra.
Qed.
