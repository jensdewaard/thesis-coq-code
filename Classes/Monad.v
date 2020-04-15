Require Export Base.
Require Import Classes.Galois List.

Implicit Type M : Type → Type.
Implicit Type T : (Type → Type) → Type → Type.
Implicit Type A B C D : Type.

Create HintDb monads.

Class Monad M : Type :=
{
  returnM : ∀ {A}, A → M A;
  bindM : ∀ {A B}, M A  → (A → M B) → M B;
  bind_id_left : ∀ {A B} (f : A → M B) (a : A), 
    bindM (returnM a) f = f a;
  bind_id_right : ∀ {A} (m : M A),
    bindM m returnM = m;
  bind_assoc : ∀ {A B C} (m : M A) (f : A → M B) (g : B → M C),
    bindM (bindM m f) g = bindM m (λ a, bindM (f a) g);
}.
Arguments bindM : simpl never.
Arguments returnM: simpl never.
Hint Unfold bindM : monads.
Hint Rewrite @bind_id_left @bind_assoc : monads.

Class bind_sound (M M' : Type → Type) {MM : Monad M} {MM' : Monad M'} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : Prop := 
  bindM_sound : ∀ {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'} 
    (m : M A) (m' : M' A') (f : A → M B) (f' : A' → M' B'),
    γ m m' → γ f f' → γ (bindM m f) (bindM m' f').
Hint Resolve bindM_sound : soundness.

Class return_sound (M M' : Type → Type) {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : Prop :=
  returnM_sound : ∀ {A A' : Type} {GA : Galois A A'} (a : A) (a' : A'),
    γ (Galois:=GA) a a' → 
    γ (Galois:=GM _ _ _) (returnM (M:=M) a) (returnM (M:=M') a').
Hint Resolve returnM_sound : soundness.

Definition join {M} `{Monad M} {A} 
  (mma : M (M A)) : M A :=
  bindM mma id.

Ltac simple_solve := autounfold with monads; intros;
  repeat (simplify; 
    autorewrite with monads in * + autounfold with monads in *;
    intros; subst
  );
  try (unfold compose, id, const; contradiction + discriminate + eauto with monads).

Ltac solve_monad := repeat (simplify; simple_solve;
  match goal with
  | |- bindM ?f _ = ?f => rewrite <- bind_id_right; f_equal
  | |- bindM ?f _ = bindM ?f _ => f_equal
  | _ => simple_solve
  end).

Notation "x >>= y" := (bindM x y) (at level 40, left associativity).
Notation "x '<-' y ; z" := (bindM y (λ x, z))
  (at level 20, y at level 100, z at level 200, only parsing).
Notation "x ;; z" := (bindM x (λ _, z))
    (at level 100, z at level 200, only parsing, right associativity).

Section MonadTransformer.

  Class MonadT T {TM : ∀ (M : Type → Type) {MM : Monad M}, Monad (T M)} : Type :=
  {
    liftT {M} {MM : Monad M} {A} : M A → T M A;
    lift_return {M} {MM : Monad M} {A} : ∀ (x : A), liftT (returnM x) = returnM x;
    lift_bind {M} {MM : Monad M} {A B} : ∀ (x : M A) (f : A → M B),
      liftT (x >>= f) = liftT x >>= (f ∘ liftT);
  }.
End MonadTransformer.
Hint Unfold liftT : monads.
Hint Rewrite @lift_return @lift_bind : monads.

Section Identity_Monad.
  Definition bind_id {A B} 
    (m : Identity A) (f : A → Identity B) : Identity B := 
      match m with
      | identity a => f a
      end.
  
  Lemma bind_id_id_left : ∀ (A B : Type) (f : A → Identity B) (a : A),
    bind_id (identity a) f = f a.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_id_id_right : ∀ (A : Type) (m : Identity A),
    bind_id m identity = m.
  Proof.
    intros. destruct m. reflexivity.
  Qed.

  Lemma bind_id_assoc : ∀ (A B C : Type) (m : Identity A)
    (f : A → Identity B) (g : B → Identity C),
    bind_id (bind_id m f) g = bind_id m (λ a : A, bind_id (f a) g).
  Proof.
    intros. destruct m; simpl. reflexivity.
  Qed.

  Lemma identity_inj : ∀ A (x y : A),
    identity x = identity y → x = y.
  Proof.
    intros A x y H. inversion H. reflexivity.
  Qed.

  Global Instance monad_identity : Monad Identity :=
  {
    bind_id_left := bind_id_id_left;
    bind_id_right := bind_id_id_right;
    bind_assoc := bind_id_assoc;
  }.
End Identity_Monad.

Section list_monad.

  Definition return_list {A} (a : A) : list A := cons a nil.

  Definition bind_list {A B} (m : list A) (f : A → list B) := flat_map f m.

  Lemma bind_list_id_left : ∀ {A B} (f : A → list B) (a : A),
    bind_list (return_list a) f = f a.
  Proof.
    intros A B f a. unfold bind_list, return_list. unfold flat_map.
    rewrite app_nil_r. reflexivity.
  Qed.

  Lemma bind_list_id_right : ∀ {A} (m : list A),
    bind_list m return_list = m.
  Proof.
    intros. unfold bind_list, return_list. induction m.
    - reflexivity.
    - simpl. rewrite IHm. reflexivity.
  Qed.

  Lemma flat_map_distr {A B} : ∀ (l l': list A) (f : A → list B),
    flat_map f (l ++ l') = flat_map f l ++ flat_map f l'.
  Proof.
    intros l l' f. generalize dependent l'. induction l.
    - simpl. reflexivity.
    - simpl. intro l'. rewrite <- app_assoc. rewrite IHl. reflexivity.
  Qed.

  Lemma bind_list_assoc : ∀ {A B C} (m : list A)
    (f : A → list B) (g : B → list C),
    bind_list (bind_list m f) g =
    bind_list m (λ a : A, bind_list (f a) g).
  Proof.
    intros A B C m f g. induction m.
    - reflexivity.
    - simpl. rewrite <- IHm. unfold bind_list. rewrite flat_map_distr.
      reflexivity.
  Qed.

  Global Instance list_monad : Monad list := {
    bind_id_left := @bind_list_id_left;
    bind_id_right := @bind_list_id_right;
    bind_assoc := @bind_list_assoc;
  }.
End list_monad.

