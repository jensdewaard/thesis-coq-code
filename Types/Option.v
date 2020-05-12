Require Export Base.
Require Import Classes.Galois Classes.Monad Classes.PreorderedSet
  Classes.Joinable Classes.Monad.MonadJoin Types.State.

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
Hint Constructors gamma_optionA : soundness.

Inductive gamma_option {A A'} {GA : Galois A A'} : option A → option A' → Prop :=
  | gamma_none : ∀ m, gamma_option None m
  | gamma_Some_Some : ∀ a' a, γ a' a → gamma_option (Some a') (Some a).
Hint Constructors gamma_option : soundness.

Instance galois_optionA : ∀ A A' (GA : Galois A A'), 
  Galois (optionA A) (option A') := @gamma_optionA.
Hint Unfold galois_optionA : soundness.

Instance galois_option : ∀ A A' (GA : Galois A A'), 
  Galois (option A) (option A') := @gamma_option.
Hint Unfold galois_option : soundness.

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
  Global Instance return_op_option : return_op option := @Some.

  Definition bind_option {A B} 
    (m : option A) (f : A -> option B) : option B :=
    match m with
    | None => None
    | Some a => f a
    end.
  Hint Unfold bind_option : monads.
  Global Instance bind_op_option : bind_op option := @bind_option.

  Lemma bind_option_id_left : ∀ {A B} (f : A → option B) (a : A), 
    bind_option (Some a) f = f a.
  Proof. 
    intros; unfold bind_option. 
    reflexivity.
  Qed.
  Arguments bind_option_id_left [A B] f a.

  Lemma bind_option_id_right : ∀ {A} (m : option A), 
    bind_option m Some = m.
  Proof. 
    intros; unfold bind_option.
    destruct m; reflexivity.
  Qed.
  Arguments bind_option_id_right [A] m.

  Lemma bind_option_assoc : ∀ {A B C} (m : option A) 
    (f : A → option B) (g : B → option C),
  bind_option (bind_option m f) g = bind_option m (λ a : A, bind_option (f a) g).
  Proof. 
    intros; unfold bind_option.
    destruct m; reflexivity.
  Qed. 
  Arguments bind_option_assoc [A B C] m f g.

  Global Instance option_monad : Monad option :=
  {
    bind_id_left := bind_option_id_left;
    bind_id_right := bind_option_id_right;
    bind_assoc := bind_option_assoc;
  }. 
End option_monad.

Instance option_ordered : OrderedMonad option.
Proof.
  split. 
  - intros A B PA PB m m' f f' Hm Hf Hff'.
    destruct m, m'; unfold bindM, bind_op_option, bind_option;
      try constructor; inversion Hm; subst. 
    apply preorder_trans with (y:=f a0); auto. 
Defined.

Instance some_sound : return_sound option option.
Proof.
  unfold return_sound; intros. 
  constructor; assumption.
Qed.
Hint Resolve some_sound : soundness.

Instance bind_option_sound : bind_sound option option.
Proof.
  unfold bind_sound; intros A A' B B' GA GB m m' f f' Hm Hf.
  unfold bindM; simpl; unfold bind_option.
  destruct m, m'; eauto with soundness. 
Qed.
Hint Resolve bind_option_sound : soundness.

Section optionA_monad.
  Global Instance return_op_optionA : return_op optionA := @SomeA.

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
  Global Instance bind_op_optionA : bind_op optionA := @bind_optionA.

  Lemma bind_optionA_id_left : ∀ {A B} (f : A → optionA B) (a : A),
  bind_optionA (SomeA a) f = f a.
  Proof. reflexivity. Qed.
  Arguments bind_optionA_id_left [A B] f a.

  Lemma bind_optionA_id_right :  ∀ {A} (m : optionA A),
    bind_optionA m SomeA = m.
  Proof. 
    intros A m; unfold bind_optionA.
    destruct m; reflexivity.
  Qed.
  Arguments bind_optionA_id_right [A].

  Lemma bind_optionA_assoc : ∀ {A B C} (m : optionA A) 
    (f : A → optionA B) (g : B → optionA C),
    bind_optionA (bind_optionA m f) g =
    bind_optionA m (λ a : A, bind_optionA (f a) g).
  Proof. 
    intros; unfold bind_optionA.
    destruct m; try reflexivity.
    destruct (f a); try reflexivity.
    destruct (g b); try reflexivity.
  Qed.
  Arguments bind_optionA_assoc [A B C] m f g.

  Global Instance optionA_monad : Monad optionA :=
  {
    bind_id_left := bind_optionA_id_left;
    bind_id_right := bind_optionA_id_right;
    bind_assoc := bind_optionA_assoc;
  }. 
End optionA_monad.

Instance optionA_ordered : OrderedMonad optionA.
Proof.
  split.
  intros A B PA PB m m' f f' Hm Hf Hff'.
  destruct m, m'; unfold bindM, bind_op_optionA, bind_optionA.
  - inversion Hm; subst.
    eapply preorder_trans with (f a0); auto. 
  - inversion Hm.
  - inversion Hm; subst.
    apply Hf in H1.
    assert (f a ⊑ f' a0) as Hf2.
    { eapply preorder_trans with (f a0); auto. }
    destruct (f' a0).
    + apply preorder_trans with (SomeA b); auto. constructor.
      apply preorder_refl.
    + inversion Hf2. apply preorder_refl.
    + assumption.
  - inversion Hm.
  - apply preorder_refl.
  - destruct (f' a); constructor.
  - inversion Hm.
  - inversion Hm.
  - inversion Hm; subst. assert (f a ⊑ f' a0) as Hb.
    { apply preorder_trans with (f a0); auto. }
    destruct (f a), (f' a0); inversion Hb; subst; constructor; assumption.
Defined.

Instance someA_sound : return_sound optionA option.
Proof.
  unfold return_sound; eauto with soundness.
Qed.
Hint Resolve someA_sound : soundness.

Instance bind_optionA_sound : bind_sound optionA option.
Proof.
  unfold bind_sound. intros A A' B B' GA GB m m' f f' Hm Hf. 
  unfold bindM; simpl. 
  destruct m as [a | |], m' as [a' |]; eauto with soundness.
  - simpl. 
    inversion Hm as [ | | | a1' a1 Ha H1 H0  ]; subst.
    apply Hf in Ha. destruct (f a), (f' a'); eauto with soundness.
  - simpl. destruct (f a); eauto with soundness.
Qed.
Hint Resolve bind_optionA_sound : soundness.

Section optionT_Monad.
  Context {M} `{MM : Monad M}.

  Definition return_optionT {A} (a : A) : optionT M A :=
    returnM (Some a).
  Global Instance return_op_optionT : return_op (optionT M) :=
    @return_optionT.

  Definition bind_optionT {A B} (m : optionT M A) 
    (f : A -> optionT M B) : optionT M B :=
    bindM (M:=M) m (λ v : option A,
      match v with
      | None => (returnM None)
      | Some a => f a
      end).
  Arguments bind_optionT [A B] m f.
  Hint Unfold bind_optionT : monads.
  Global Instance bind_op_optionT : bind_op (optionT M) :=
    @bind_optionT.

  Lemma bind_optionT_id_left : ∀ {A B} (f : A → optionT M B) (a : A), 
    bind_optionT (return_optionT a) f = f a.
  Proof. 
    intros. unfold bind_optionT, return_optionT.
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_optionT_id_left [A B] f a.

  Lemma bind_optionT_id_right : ∀ {A} (m : optionT M A),
    bind_optionT m (λ a, return_optionT a) = m.
  Proof. 
    intros; unfold bind_optionT, return_optionT.
    rewrite <- (bind_id_right (M:=M)); f_equal. 
    ext; destruct x; reflexivity.
  Qed.
  Arguments bind_optionT_id_right [A] m.

  Lemma bind_optionT_assoc : ∀ {A B C} (m : optionT M A) 
    (f : A → optionT M B) (g : B → optionT M C),
    bind_optionT (bind_optionT m f) g =
    bind_optionT m (λ a : A, bind_optionT (f a) g).
  Proof. 
    intros; unfold bind_optionT. 
    rewrite bind_assoc; f_equal; extensionality x. 
    destruct x; eauto with monads.
    rewrite bind_id_left; reflexivity.
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

(*Definition optionT_le {M} {PM : ∀ A, PreorderedSet A → PreorderedSet (M A)} 
  {BO : bind_op M} {RO : return_op M}
  {A} (m1 m2 : optionT M A) : Prop :=
  m1 >>= (λ o1, *)

Instance optionT_preorder : ∀ {M}
  {PM : ∀ A, PreorderedSet A → PreorderedSet (M A)},
  (∀ A, PreorderedSet A → PreorderedSet (optionT M A)).
Proof.
  intros M PM A PA. unfold optionT. apply PM. apply option_preorder.
Defined.

Instance monad_optionT_ordered {S} {PS : PreorderedSet S} :
  OrderedMonad (optionT (State S)).
Proof.
  split. 
  - intros A B PA PB m m' f f' Hm Hf Hff'.
    unfold bindM, bind_op_optionT, bind_optionT.
    unfold bindM, bind_op_state, bind_state.
    unfold preorder; simpl; constructor; intro s.
    inversion Hm as [f2' g Hm' H0 H1]; subst.
    assert (m s ⊑ m' s) as Hms. apply Hm'.
    destruct (m s), (m' s). 
    destruct o, o0. 
Admitted.

Instance optionAT_preorder : ∀ {M}
  {PM : ∀ A, PreorderedSet A → PreorderedSet (M A)},
  (∀ A, PreorderedSet A → PreorderedSet (optionAT M A)).
Proof.
  intros M PM A PA. unfold optionAT. apply PM. apply optionA_preorder.
Defined.

Definition return_optionAT {M} {RM : return_op M} A (a : A) : optionAT M A :=
  returnM (SomeA a).
Instance return_op_optionAT_state {M} {RM : return_op M} : 
  return_op (optionAT M) := return_optionAT.
Arguments return_optionAT {M RM A} a.

Section optionAT_state_monad.
  Context {S} {JS : Joinable S S} {JI : JoinableIdem JS}.

  Definition bind_optionAT_state {A B} 
    (m : optionAT (State S) A)
    (f : A -> optionAT (State S) B) : optionAT (State S) B :=
  λ s : S, let (o, s') := m s in 
    match o with
    | NoneA => (NoneA, s')
    | SomeA x => f x s'
    | SomeOrNoneA x => let (o', s'') := (f x s') in
                             match o' with 
                             | NoneA => (NoneA, s' ⊔ s'')
                             | SomeA x' => (SomeOrNoneA x', s' ⊔ s'')
                             | SomeOrNoneA x' => (SomeOrNoneA x', s' ⊔ s'')
                             end
    end.
  Hint Unfold bind_optionAT_state : monads.
  Global Instance bind_op_optionAT_state : bind_op (optionAT (State S)) :=
    @bind_optionAT_state.

  Lemma bind_optionAT_state_id_left : ∀ {A B} (f : A → optionAT (State S) B) (a : A), 
    bind_optionAT_state (return_optionAT a) f = f a.
  Proof. 
    intros; unfold bind_optionAT_state, return_optionAT.
    reflexivity.
  Qed.
  Arguments bind_optionAT_state_id_left [A B] f a.

  Lemma bind_optionAT_state_id_right : ∀ (A : Type) (m : optionAT (State S) A), 
    bind_optionAT_state m (λ a, return_optionAT  a) = m.
  Proof. 
    intros; unfold bind_optionAT_state, return_optionAT; extensionality s.
    destruct (m s) as [o s'].
    unfold returnM, return_op_state, return_state.
    destruct o; try reflexivity.
    rewrite JI; reflexivity.
  Qed.

  Lemma bind_optionAT_state_assoc : ∀ {A B C} (m : optionAT (State S) A) 
    (f : A → optionAT (State S) B) (g : B → optionAT (State S) C),
    bind_optionAT_state (bind_optionAT_state m f) g =
    bind_optionAT_state m (λ a : A, bind_optionAT_state (f a) g).
  Proof. 
    intros; unfold bind_optionAT_state. 
    extensionality s.
    destruct (m s) as [o s'] eqn:Hms.
    destruct o as [x |  | x].
    - destruct (f x s') as [o' s''] eqn:Hfxs.
      destruct o'; reflexivity.
    - reflexivity.
    - (* m f = (SomeOrNoneA, ) *) 
      destruct (f x s') as [o s''] eqn:Hfxs.
      destruct o.
      + destruct (g b (s' ⊔ s'')) eqn:Hqbs''.
        destruct (g b s'') eqn:Hqbs'.
  Admitted.
  Arguments bind_optionAT_state_assoc [A B C] m f g.

Global Instance monad_optionAT : Monad (optionAT (State S)) :=
  {
    bind_id_left := bind_optionAT_state_id_left;
    bind_id_right := bind_optionAT_state_id_right;
    bind_assoc := bind_optionAT_state_assoc;
  }.

End optionAT_state_monad.
Hint Unfold bind_optionAT_state : monads.

Instance return_optionAT_sound {M M'} `{RS : return_sound M M'} :
  return_sound (optionAT M) (optionT M').
Proof.
  unfold return_sound, returnM; simpl. eauto with soundness.
Qed.

Section optionAT_state_sound.
  Context {S : Type} {JS : Joinable S S} {JI : JoinableIdem JS}.
  Context {S' : Type} {GS : Galois S S'}.
  Context {JSS : JoinableSound JS}.

  Global Instance bind_optionAT_state_sound :
    bind_sound (optionAT (State S)) (optionT (State S')).
  Proof.
    intros A A' B B' GA GB m m' f f' Hm Hf. 
    unfold bindM; simpl. 
    unfold bind_op_optionAT_state, bind_optionAT_state.
    unfold bind_op_optionT, bind_optionT.
    unfold bindM; simpl; unfold bind_op_state, bind_state.
    intros s s' Hs. 
    apply Hm in Hs; destruct (m s) as [o s2], (m' s') as [o' s2'].
    inversion Hs as [? ? Ho Hs2 H1 H2]; simpl in *; subst; clear Hs.
    destruct o as [a| |a], o' as [a'|].
    - inversion Ho as [| | ? ? Ha |]; subst; clear Ho.
      apply Hf in Ha; apply Ha in Hs2; assumption.
    - inversion Ho.
    - inversion Ho.
    - unfold returnM; simpl; unfold return_state. 
      constructor; simpl.
      * constructor.
      * assumption.
    - (* SomeOrNoneA, Some *) inversion Ho as [| | | ?? Ha H0 H1]; subst; clear Ho.
      apply Hf in Ha; apply Ha in Hs2.
      destruct (f a s2) as [o s3], (f' a' s2') as [o' s3'].  
      inversion Hs2 as [?? Ho Hs3 H1 H2]; subst; simpl in *; clear Hs2.
      destruct o, o'; simpl.
      + constructor; simpl. constructor. inversion Ho; subst. assumption.
        apply join_sound; right; assumption.
      + inversion Ho; subst. 
      + inversion Ho.
      + constructor; simpl. 
        * constructor.
        * apply join_sound; right; assumption.
      + constructor; simpl. 
        * assumption.
        * apply join_sound; right; assumption.
      + constructor; simpl.
        * assumption.
        * apply join_sound; right; assumption.
    - (* SomeOrNoneA, None *) unfold returnM; simpl; unfold return_state.
      destruct (f a s2) eqn:?.
      destruct o; simpl. 
      + constructor; simpl. 
        * constructor.
        * apply join_sound; left; assumption.
      + constructor; simpl.
        * constructor.
        * apply join_sound; left; assumption.
      + constructor; simpl.
        * constructor.
        * apply join_sound; left; assumption.
  Qed.
End optionAT_state_sound.

Section optionAT_stateT_monad.
  Context {S} {JS : Joinable S S} {JI : JoinableIdem JS}.
  Context {M} {RO : return_op M} {BO : bind_op M} {MM : Monad M}.

  Definition bind_optionAT_stateT {A B} 
    (m : optionAT (StateT S M) A)
    (f : A -> optionAT (StateT S M) B) : optionAT (StateT S M) B :=
  λ s : S, m s >>= λ '(o, s'),
    match o with
    | NoneA => returnM (NoneA, s')
    | SomeA x => (f x s')
    | SomeOrNoneA x => (f x s') >>= λ '(o', s''),
                             match o' with 
                             | NoneA => returnM (NoneA, s' ⊔ s'')
                             | SomeA x' => returnM (SomeOrNoneA x', s' ⊔ s'')
                             | SomeOrNoneA x' => returnM (SomeOrNoneA x', s' ⊔ s'')
                             end
    end.
  Hint Unfold bind_optionAT_stateT : monads.
  Global Instance bind_op_optionAT_stateT :
    bind_op (optionAT (StateT S M)) := @bind_optionAT_stateT.

  Lemma bind_optionAT_stateT_id_left : ∀ {A B} 
    (f : A → optionAT (StateT S M) B) (a : A), 
    bind_optionAT_stateT (return_optionAT a) f = f a.
  Proof. 
    unfold bind_optionAT_stateT, return_optionAT; simpl; intros. 
    unfold returnM, return_op_stateT, return_stateT.
    extensionality s. 
    rewrite bind_id_left; reflexivity.
  Qed.
  Arguments bind_optionAT_stateT_id_left [A B] f a.

  Lemma bind_optionAT_stateT_id_right : ∀ (A : Type) 
    (m : optionAT (StateT S M) A), 
    bind_optionAT_stateT m (λ a, return_optionAT a) = m.
  Proof. 
    unfold bind_optionAT_stateT; intros. 
    unfold return_optionAT, returnM, return_op_stateT, return_stateT.
    extensionality s.
    rewrite <- bind_id_right; f_equal.
    extensionality p; destruct p, o.
    1, 2: reflexivity. 
    rewrite bind_id_left, JI; reflexivity.
  Qed.

  Lemma bind_optionAT_stateT_assoc : ∀ {A B C} 
    (m : optionAT (StateT S M) A) 
    (f : A → optionAT (StateT S M) B) 
    (g : B → optionAT (StateT S M) C),
    bind_optionAT_stateT (bind_optionAT_stateT m f) g =
    bind_optionAT_stateT m (λ a : A, bind_optionAT_stateT (f a) g).
  Proof. 
    intros; unfold bind_optionAT_stateT. 
    extensionality s.
    rewrite bind_assoc; f_equal; extensionality p. 
    destruct p, o.
  Admitted.
  Arguments bind_optionAT_stateT_assoc [A B C] m f g.

  Global Instance monad_optionAT_stateT : Monad (optionAT (StateT S M)) :=
  {
    bind_id_left := bind_optionAT_stateT_id_left;
    bind_id_right := bind_optionAT_stateT_id_right;
    bind_assoc := bind_optionAT_stateT_assoc;
  }.

  Context {PS : PreorderedSet S}.
  Context {PM : forall A, PreorderedSet A -> PreorderedSet (M A)}.

  Instance preordered_optionAT : 
    ∀ A, PreorderedSet A →
    PreorderedSet (optionAT (StateT S M) A) :=
  {
    preorder := preorder;
    preorder_refl := preorder_refl;
    preorder_trans := preorder_trans;
  }.

  Instance ordered_optionAT_stateT : 
    OrderedMonad M →
    OrderedMonad (optionAT (StateT S M)).
  Proof.
    intros OM; split. 
    - intros A PA a1 a2 Ha; constructor; intros s. 
      unfold returnM, return_op_optionAT_state, return_optionAT.
      unfold returnM, return_op_stateT, return_stateT.
  Admitted.
End optionAT_stateT_monad.

Section optionAT_stateT_sound.
  Context {S : Type} {JS : Joinable S S} {JI : JoinableIdem JS}.
  Context {S' : Type} {GS : Galois S S'}.
  Context {JSS : JoinableSound JS}.

  Global Instance bind_optionAT_stateT_sound :
    bind_sound (optionAT (StateT S option)) (optionT (StateT S' option)).
  Proof.
    intros A A' B B' GA GB m m' f f' Hm Hf. 
    unfold bindM; simpl. 
    unfold bind_op_optionAT_stateT, bind_op_optionT, 
      bind_optionAT_stateT, bind_optionT.
    unfold bindM at 3; unfold bind_op_stateT, bind_stateT.
    intros s s' Hs. 
    apply Hm in Hs; destruct (m s) as [[o s2]|]; 
        destruct (m' s') as [[o' s2']|].
    - inversion Hs as [| a a' Hp Hsss Haq]; subst.
      inversion Hp as [? ? Ho Hs2]; subst; clear Hs Hp; simpl in *.
      apply bindM_sound. constructor; constructor; assumption.
      intros [x s3] [x' s3'] Hpq. 
      inversion Hpq as [p q Hx Hs3 H2 H3]; subst; simpl in *; clear Hpq.
      destruct x as [a| |a], x' as [a'|].
      + simpl; apply Hf. 
        * inversion Hx; subst; assumption.
        * assumption.
      + inversion Hx.
      + inversion Hx.
      + apply some_sound. constructor; simpl.
        * constructor.
        * assumption.
      + unfold bindM, bind_op_option, bind_option. 
        inversion Hx as [| |  | ? ? Ha Heqa0 Heqa]; subst. 
        apply Hf in Ha. apply Ha in Hs3.
        destruct (f a s3) as [p|], (f' a' s3') as [p'|].
        * destruct p as [a2 s4], p' as [a2' s4'].
          inversion Hs3 as [| ? ? Hp H H0]; subst.
          inversion Hp as [p q Ha2 Hs4 H1 H2]; subst; simpl in *; clear Hp Hs3.
          destruct a2.
          -- constructor; constructor; simpl.
             ++ destruct a2'; constructor. 
                inversion Ha2; subst; assumption. 
             ++ apply join_sound; right; assumption.
          -- constructor; constructor; simpl.
             ++ assumption.
             ++ apply join_sound; right; assumption.
          -- constructor; constructor; simpl. 
             ++ assumption.
             ++ apply join_sound; right; assumption.
        * inversion Hs3. 
        * constructor.
        * constructor.
      + unfold bindM, bind_op_option, bind_option.
        destruct (f a s3).
        * destruct p as [o2 s4]; destruct o2; constructor; constructor; 
            try constructor; simpl; apply join_sound; left; assumption.
        * constructor.
    - inversion Hs.
    - constructor. 
    - constructor.
  Qed.
End optionAT_stateT_sound.

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
