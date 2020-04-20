Require Export Base.
Require Import Classes.Galois Classes.Monad Classes.PreorderedSet
  Classes.Joinable Classes.Monad.MonadJoin.

Inductive optionA (A : Type) : Type :=
  | SomeA : A → optionA A
  | NoneA : optionA A
  | SomeOrNoneA : A → optionA A.
Arguments SomeA {A} a.
Arguments NoneA {A}.
Arguments SomeOrNoneA {A} a.
Definition optionT (M : Type → Type) (A : Type) : Type := M (option A).
Definition optionAT (M : Type → Type) (A : Type) : Type := M (optionA A).

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

Section option_preorder.
  Context {A} `{A_preorder : PreorderedSet A}.

  Inductive option_le : option A → option A → Prop :=
    | option_le_none : ∀ m, option_le m None
    | option_le_just : ∀ x y, preorder x y → option_le (Some x) (Some y).
  Hint Constructors option_le : preorders.

  Global Instance option_preorder : PreorderedSet (option A).
  Proof. proof_preorder option_le. Defined.
End option_preorder.
Hint Constructors option_le : preorders.

Section optionA_preorder.
  Context {A : Type} `{A_preorder : PreorderedSet A}.

  Inductive optionA_le : optionA A → optionA A → Prop :=
    | optionA_le_none : optionA_le NoneA NoneA
    | optionA_le_none_justornone : ∀ y, optionA_le NoneA (SomeOrNoneA y)
    | optionA_le_just : ∀ x y, preorder x y → optionA_le (SomeA x) (SomeA y)
    | optionA_le_justornone_r : ∀ x y, preorder x y →
        optionA_le (SomeA x) (SomeOrNoneA y)
    | optionA_le_justornone : ∀ x y, preorder x y →
        optionA_le (SomeOrNoneA x) (SomeOrNoneA y).
  Hint Constructors optionA_le : preorders.

  Global Instance optionA_preorder : PreorderedSet (optionA A).
  Proof. proof_preorder optionA_le. Defined.
End optionA_preorder.
Hint Constructors optionA_le : preorders.

Section option_monad.
  Definition bind_option {A B} 
    (m : option A) (f : A -> option B) : option B :=
    match m with
    | None => None
    | Some a => f a
    end.
  Hint Unfold bind_option : monads.

  Lemma bind_option_id_left : ∀ {A B} (f : A → option B) (a : A), 
    bind_option (Some a) f = f a.
  Proof. simple_solve. Qed.
  Arguments bind_option_id_left [A B] f a.

  Lemma bind_option_id_right : ∀ {A} (m : option A), 
    bind_option m Some = m.
  Proof. simple_solve. Qed.
  Arguments bind_option_id_right [A] m.

  Lemma bind_option_assoc : ∀ {A B C} (m : option A) 
    (f : A → option B) (g : B → option C),
  bind_option (bind_option m f) g = bind_option m (λ a : A, bind_option (f a) g).
  Proof. simple_solve. Qed.
  Arguments bind_option_assoc [A B C] m f g.

  Global Instance option_monad : Monad option :=
  {
    bind_id_left := bind_option_id_left;
    bind_id_right := bind_option_id_right;
    bind_assoc := bind_option_assoc;
  }. 
End option_monad.

Section optionA_monad.
  Definition bind_optionA {A B : Type}
    (m : optionA A) (f : A -> optionA B) : optionA B :=
    match m with
    | NoneA => NoneA
    | SomeA a => f a
    | SomeOrNoneA a => match (f a) with
                       | NoneA => NoneA
                       | SomeA b => SomeOrNoneA b
                       | SomeOrNoneA b => SomeOrNoneA b
                       end
    end.
  Arguments bind_optionA [_ _].
  Hint Unfold bind_optionA : monads.

  Lemma bind_optionA_id_left : ∀ {A B} (f : A → optionA B) (a : A),
  bind_optionA (SomeA a) f = f a.
  Proof. simple_solve. Qed.
  Arguments bind_optionA_id_left [A B] f a.

  Lemma bind_optionA_id_right :  ∀ {A} (m : optionA A),
    bind_optionA m SomeA = m.
  Proof. simple_solve. Qed.
  Arguments bind_optionA_id_right [A].

  Lemma bind_optionA_assoc : ∀ {A B C} (m : optionA A) 
    (f : A → optionA B) (g : B → optionA C),
    bind_optionA (bind_optionA m f) g =
    bind_optionA m (λ a : A, bind_optionA (f a) g).
  Proof. solve_monad. Qed.
  Arguments bind_optionA_assoc [A B C] m f g.

  Global Instance optionA_monad : Monad optionA :=
  {
    bind_id_left := bind_optionA_id_left;
    bind_id_right := bind_optionA_id_right;
    bind_assoc := bind_optionA_assoc;
  }. 
End optionA_monad.

Section optionT_Monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_optionT {A B} (m : optionT M A) 
    (f : A -> optionT M B) : optionT M B :=
    bindM (M:=M) m (λ v : option A,
      match v with
      | None => (returnM None)
      | Some a => f a
      end).
  Arguments bind_optionT [A B] m f.
  Hint Unfold bind_optionT : monads.

  Lemma bind_optionT_id_left : ∀ {A B} (f : A → optionT M B) (a : A), 
    bind_optionT (returnM (M:=M) (Some a)) f = f a.
  Proof. 
    intros. unfold bind_optionT.
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_optionT_id_left [A B] f a.

  Lemma bind_optionT_id_right : ∀ {A} (m : optionT M A),
    bind_optionT m (λ a, returnM (M:=M) (Some a)) = m.
  Proof. 
    intros. unfold bind_optionT.
    rewrite <- (bind_id_right (M:=M)). f_equal. 
    ext; destruct x; reflexivity.
  Qed.
  Arguments bind_optionT_id_right [A] m.

  Lemma bind_optionT_assoc : ∀ {A B C} (m : optionT M A) 
    (f : A → optionT M B) (g : B → optionT M C),
    bind_optionT (bind_optionT m f) g =
    bind_optionT m (λ a : A, bind_optionT (f a) g).
  Proof. 
    intros. unfold bind_optionT. autorewrite with monads.
    f_equal. ext. destruct x; eauto with monads.
    autorewrite with monads. reflexivity.
  Qed.
  Arguments bind_optionT_assoc [A B C] m f g.

  Global Instance monad_optionT : Monad (optionT M) :=
  {
    bind_id_left := bind_optionT_id_left;
    bind_id_right := bind_optionT_id_right;
    bind_assoc := bind_optionT_assoc;
  }. 
End optionT_Monad.
Hint Unfold bind_optionT : monads.
Hint Rewrite @bind_optionT_id_left @bind_optionT_id_right : monads.

Section optionAT_monad.
  Context {M} {MM : Monad M} {JM : joinsecondable M}.

  Definition lub {A} (y : optionA A) : optionA A := 
    match y with
    | NoneA => NoneA
    | SomeA a | SomeOrNoneA a => SomeOrNoneA a
    end.

  Definition bind_optionAT {A B} 
    (Mma : optionAT M A)
    (f : A -> optionAT M B) : optionAT M B :=
  bindM (M:=M) Mma (fun ma =>
    match ma with
    | NoneA => returnM NoneA
    | SomeA a => f a
    | SomeOrNoneA a => joinsecond lub (f a)
    end).
  Hint Unfold bind_optionAT : monads.

  Lemma bind_optionAT_id_left : ∀ {A B} (f : A → optionAT M B) (a : A), 
    bind_optionAT (returnM (M:=M) (SomeA a)) f = f a.
  Proof. 
    unfold bind_optionAT; simpl. intros.
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_optionAT_id_left [A B] f a.

  Lemma bind_optionAT_id_right : ∀ (A : Type) (m : optionAT M A), 
    bind_optionAT m (λ a, returnM (M:=M) (SomeA a))= m.
  Proof. 
    unfold bind_optionAT.  intros. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality x. 
    destruct x; autorewrite with monads; try reflexivity. 
    rewrite joinsecond_return. reflexivity.
  Qed.

  Lemma bind_optionAT_assoc : ∀ {A B C} (m : optionAT M A) 
    (f : A → optionAT M B) (g : B → optionAT M C),
    bind_optionAT (bind_optionAT m f) g =
    bind_optionAT m (λ a : A, bind_optionAT (f a) g).
  Proof. 
    intros. unfold bind_optionAT. autorewrite with monads.
    f_equal; ext. destruct x; simpl. 
    1-2: autorewrite with monads; reflexivity.
    apply joinsecond_bind. 
    destruct x; simpl. 
    - reflexivity.
    - rewrite joinsecond_return. reflexivity.
    - rewrite <- joinsecond_compose. f_equal. ext. destruct x; reflexivity.
  Qed.
  Arguments bind_optionAT_assoc [A B C] m f g.

  Global Instance monad_optionAT : Monad (optionAT M) :=
  {
    bind_id_left := bind_optionAT_id_left;
    bind_id_right := bind_optionAT_id_right;
    bind_assoc := bind_optionAT_assoc;
  }.
End optionAT_monad.
Hint Unfold bind_optionAT : monads.

Definition mjoin_option A {JA : Joinable A A} {JI : JoinableIdem JA} : 
  option A → option A → option A :=
  λ m1 : option A, λ m2 : option A,
    match m1, m2 with
    | Some x, Some y => Some (x ⊔ y)
    | _, _ => None
    end.

Instance option_monadjoin : MonadJoin option.
Proof.
  split with mjoin_option. reflexivity.
Defined.
Hint Resolve option_monadjoin : soundness.

Instance option_monadjoin_sound : MonadJoinSound option option.
Proof.
  constructor; intros.
  - destruct m1, m2; try constructor. destruct m'.
    + constructor. apply join_sound.  constructor. inversion H;subst.
      apply H2.
    + inversion H.
  - destruct m1, m2; try constructor. destruct m'.
    + constructor. apply join_sound. right. inversion H; subst.
      apply H2.
    + inversion H. 
Qed.
