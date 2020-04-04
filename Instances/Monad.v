Require Export Base.
Require Export Classes.Monad.
Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Import Language.Statements.
Require Import Types.Maps.
Require Import Types.State.

Implicit Type S A B C : Type.
Implicit Type M : Type → Type.

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
  Hint Unfold bind_optionT : soundness.

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
    intros. unfold bind_optionT. autorewrite with soundness.
    f_equal. ext. destruct x; eauto with soundness.
    autorewrite with soundness. reflexivity.
  Qed.
  Arguments bind_optionT_assoc [A B C] m f g.

  Global Instance monad_optionT : Monad (optionT M) :=
  {
    bind_id_left := bind_optionT_id_left;
    bind_id_right := bind_optionT_id_right;
    bind_assoc := bind_optionT_assoc;
  }. 
End optionT_Monad.
Hint Unfold bind_optionT : soundness.
Hint Rewrite @bind_optionT_id_left @bind_optionT_id_right : soundness.

Section optionT_monadT.
  Definition lift_optionT {M : Type → Type} `{Monad M} {A} (m : M A) : optionT M A :=
    bindM (M:=M) m (λ a, returnM (Some a)).
  Hint Unfold lift_optionT : soundness.

  Lemma lift_optionT_pure {M : Type → Type} `{Monad M} : ∀ {A : Type} (a : A),
    lift_optionT (returnM (M:=M) a) = returnM (M:=M) (Some a).
  Proof. 
    intros. unfold lift_optionT. 
    rewrite bind_id_left. reflexivity.
  Qed.

  Lemma lift_optionT_bind {M : Type → Type} `{Monad M} : 
    ∀ (A B : Type) (m : M A) (f : A → M B),
  lift_optionT (m >>= f) = bind_optionT (lift_optionT m) (f ∘ (lift_optionT (A:=B))).
  Proof. 
    intros. unfold lift_optionT, bind_optionT.
    autorewrite with soundness. f_equal; ext. autorewrite with soundness.
    reflexivity.
  Qed.

  Global Instance monadT_optionT : MonadT (optionT) :=
  {
    lift_return := @lift_optionT_pure;
    lift_bind := @lift_optionT_bind;
  }. 
End optionT_monadT.

Section optionAT_monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_optionAT {A B} 
    (Mma : optionAT M A)
    (f : A -> optionAT M B) : optionAT M B :=
  bindM (M:=M) Mma (fun ma =>
    match ma with
    | NoneA => returnM NoneA
    | SomeA a => f a
    | SomeOrNoneA a => (
        bindM (M:=M) (f a) (fun mfa =>
                       match mfa with
                       | NoneA => returnM NoneA
                       | SomeA b => returnM (SomeOrNoneA b)
                       | SomeOrNoneA b => returnM (SomeOrNoneA b)
                       end))
    end).
  Hint Unfold bind_optionAT : soundness.

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
    destruct x; autorewrite with soundness; try reflexivity.
  Qed.

  Lemma bind_optionAT_assoc : ∀ {A B C} (m : optionAT M A) 
    (f : A → optionAT M B) (g : B → optionAT M C),
    bind_optionAT (bind_optionAT m f) g =
    bind_optionAT m (λ a : A, bind_optionAT (f a) g).
  Proof. 
    intros. unfold bind_optionAT. autorewrite with soundness.
    f_equal; ext. destruct x; simpl. 
    1-2: autorewrite with soundness; reflexivity.
    autorewrite with soundness. f_equal; ext.
    destruct x; autorewrite with soundness. 
    f_equal. reflexivity. f_equal; ext.
    destruct x; autorewrite with soundness; reflexivity.
  Qed.
  Arguments bind_optionAT_assoc [A B C] m f g.

  Global Instance monad_optionAT : Monad (optionAT M) :=
  {
    bind_id_left := bind_optionAT_id_left;
    bind_id_right := bind_optionAT_id_right;
    bind_assoc := bind_optionAT_assoc;
  }. 
End optionAT_monad.
Hint Unfold bind_optionAT : soundness.

Section optionAT_MonadT.
  Definition lift_optionAT {M} `{Monad M} {A} (m : M A) : optionAT M A :=
    bindM (M:=M) m (λ a, returnM (M:=M) (SomeA a)).
  Hint Unfold lift_optionAT : soundness.

  Definition lift_optionAT_pure {M} `{Monad M} {A} : ∀ (a : A),
    lift_optionAT (returnM a) = returnM a.
  Proof. solve_monad. Qed.

  Definition lift_optionAT_bind {M} `{Monad M} {A B}: ∀ (m : M A) (f : A → M B),
    lift_optionAT (m >>= f) = bind_optionAT (lift_optionAT m) (f ∘ lift_optionAT (A:=B)).
  Proof. 
    unfold lift_optionAT, bind_optionAT. intros.
    autorewrite with soundness. f_equal; ext. autorewrite with soundness.
    reflexivity.
  Qed.

  Global Instance monadT_optionAT : MonadT optionAT :=
  {
    lift_return := @lift_optionAT_pure;
    lift_bind := @lift_optionAT_bind;
  }. 
End optionAT_MonadT.

