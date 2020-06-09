Require Export Base.
Require Import Classes.Galois List.
Require Import Classes.PreorderedSet.

Implicit Type M : Type → Type.
Implicit Type T : (Type → Type) → Type → Type.
Implicit Type A B C D : Type.

Create HintDb monads.

Class return_op (M : Type → Type) : Type := returnM : ∀ {A}, A → M A.
Class bind_op (M : Type → Type) : Type := bindM : ∀ {A B},
  M A → (A → M B) → M B.

Notation "x >>= y" := (bindM x y) (at level 40, left associativity).
Notation "x '<-' y ; z" := (bindM y (λ x, z))
  (at level 20, y at level 100, z at level 200, only parsing).
Notation "x ;; z" := (bindM x (λ _, z))
    (at level 100, z at level 200, only parsing, right associativity).

Class Monad M {RO : return_op M} {BO : bind_op M} : Type :=
{
  bind_id_left : ∀ {A B} (f : A → M B) (a : A), 
    (returnM a) >>= f = f a;
  bind_id_right : ∀ {A} (m : M A),
    m >>= returnM = m;
  bind_assoc : ∀ {A B C} (m : M A) (f : A → M B) (g : B → M C),
    (m >>= f) >>= g = m >>= (λ a, (f a) >>= g);
}.

Class OrderedMonad M {RO : return_op M} {BO : bind_op M} 
  {MO : ∀ {A}, PreorderedSet A -> PreorderedSet (M A)} : Type :=
{
  return_monotone : ∀ {A} {PA : PreorderedSet A} (a a' : A),
    a ⊑ a' → returnM a ⊑ returnM a';
  bind_monotone : ∀ {A B} {PA : PreorderedSet A} {PB : PreorderedSet B} 
   (m m' : M A) (f f' : A → M B),
   m ⊑ m' → 
   monotone f → 
   monotone f' →
   (∀ a : A, (f a) ⊑ (f' a)) →
   (m >>= f) ⊑ (m' >>= f');
}.

Class LaxMonad M `{OM : OrderedMonad M} : Type :=
{
  bind_id_left_lax : ∀ {A B} {PA : PreorderedSet A} {PB : PreorderedSet B}
    (f : A → M B) (a : A),
    ((returnM a) >>= f) = (f a);
  bind_id_right_lax : ∀ {A} {PA : PreorderedSet A} (m : M A),
    (m >>= returnM) = m;
  bind_assoc_lax : ∀ {A B C} {PB : PreorderedSet B} {PC : PreorderedSet C}
    (m : M A) (f : A → M B) (g : B → M C),
      ((m >>= f) >>= g) ⊑ (m >>= (λ a, (f a) >>= g));
}.

Arguments bindM : simpl never.
Arguments returnM: simpl never.
Hint Unfold bindM : monads.
Hint Rewrite @bind_id_left @bind_assoc : monads.

Class bind_sound (M M' : Type → Type) {MB : bind_op M} {MB' : bind_op M'} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : Prop := 
  bindM_sound : ∀ {A A' B B' : Type} {GA : Galois A A'} {GB : Galois B B'} 
    (m : M A) (m' : M' A') (f : A → M B) (f' : A' → M' B'),
    γ m m' → γ f f' → γ (m >>= f) (m' >>= f').
Hint Resolve bindM_sound : soundness.

Class return_sound (M M' : Type → Type) {MR : return_op M} {MR' : return_op M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : Prop :=
  returnM_sound : ∀ {A A' : Type} {GA : Galois A A'} (a : A) (a' : A'),
    γ a a' → 
    γ (returnM a) (returnM a').
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

Section Identity_Monad.
  Global Instance return_op_id : return_op Identity := 
    λ (A : Type) (a : A), identity a.

  Global Instance bind_op_id : bind_op Identity := λ A B 
    (m : Identity A) (f : A → Identity B),
      match m with
      | identity a => f a
      end.
  Arguments return_op_id [A] a.
  Arguments bind_op_id [A B] m f.
  
  Lemma bind_id_id_left : ∀ (A B : Type) (f : A → Identity B) (a : A),
    bind_op_id (identity a) f = f a.
  Proof. easy. Qed.

  Lemma bind_id_id_right : ∀ (A : Type) (m : Identity A),
    bind_op_id m identity = m.
  Proof.
    intros. 
    destruct m; easy.
  Qed.

  Lemma bind_id_assoc : ∀ (A B C : Type) (m : Identity A)
    (f : A → Identity B) (g : B → Identity C),
    bind_op_id (bind_op_id m f) g = bind_op_id m (λ a : A, bind_op_id (f a) g).
  Proof.
    intros. 
    destruct m; easy.
  Qed.

  Global Instance monad_identity : Monad Identity :=
  {
    bind_id_left := bind_id_id_left;
    bind_id_right := bind_id_id_right;
    bind_assoc := bind_id_assoc;
  }.

  Global Instance ordered_identity : OrderedMonad Identity.
  Proof.
    split.
    - intros A PA a a' Ha; apply Ha.
    - intros A B PA PB m m' f f' Hm Hf Hf' Hff'.
      unfold bindM, bind_op_id.
      destruct m as [a], m' as [a']; simpl in Hm. 
      eapply preorder_trans with (f a'); auto.
  Qed.

  Global Instance return_id_sound :
    return_sound Identity Identity.
  Proof.
    intros A A' GA a a' Ha. 
    apply Ha.
  Qed.

  Global Instance bind_id_sound :
    bind_sound Identity Identity.
  Proof.
    intros A A' B B' GA GB m m' f f' Hm Hf.
    destruct m as [a], m' as [a']; cbv.
    unfold γ, galois_identity, gamma_identity in Hm.
    apply Hf in Hm.
    destruct (f a) as [b], (f' a') as [b']. 
    apply Hm.
  Qed.
End Identity_Monad.

Section list_monad.
  Definition return_list {A} (a : A) : list A := cons a nil.
  Instance return_op_list : return_op list := @return_list.

  Definition bind_list {A B} (m : list A) (f : A → list B) := flat_map f m.
  Instance bind_op_list : bind_op list := @bind_list.

  Lemma bind_list_id_left : ∀ {A B} (f : A → list B) (a : A),
    bind_list (return_list a) f = f a.
  Proof.
    intros A B f a; unfold bind_list, return_list; simpl.
    rewrite app_nil_r; reflexivity.
  Qed.

  Lemma bind_list_id_right : ∀ {A} (m : list A),
    bind_list m return_list = m.
  Proof.
    intros. unfold bind_list, return_list. 
    induction m.
    - easy.
    - simpl; rewrite IHm; reflexivity.
  Qed.

  Lemma flat_map_distr {A B} : ∀ (l l': list A) (f : A → list B),
    flat_map f (l ++ l') = flat_map f l ++ flat_map f l'.
  Proof.
    intros l l' f; generalize dependent l'. 
    induction l; intros l'.
    - easy.
    - simpl. rewrite <- app_assoc. rewrite IHl. reflexivity.
  Qed.

  Lemma bind_list_assoc : ∀ {A B C} (m : list A)
    (f : A → list B) (g : B → list C),
    bind_list (bind_list m f) g =
    bind_list m (λ a : A, bind_list (f a) g).
  Proof.
    intros A B C m f g; unfold bind_list.
    induction m; simpl.
    - reflexivity.
    - rewrite <- IHm. 
      apply flat_map_distr.
  Qed.

  Global Instance list_monad : Monad list := {
    bind_id_left := @bind_list_id_left;
    bind_id_right := @bind_list_id_right;
    bind_assoc := @bind_list_assoc;
  }.
End list_monad.

