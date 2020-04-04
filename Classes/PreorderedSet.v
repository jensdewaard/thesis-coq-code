Require Export Base.
Require Import Classes.Galois Psatz.

Create HintDb preorders.

Class PreorderedSet (A : Type) : Type :=
{
  preorder : A -> A -> Prop;
  preorder_refl: ∀ x, preorder x x;
  preorder_trans: ∀ x y z, preorder x y -> preorder y z -> preorder x z;
}.
Infix "⊑" := preorder (at level 40).
Hint Resolve preorder_refl preorder_trans : preorders.

Class PreorderSound (A B : Type) `{PreorderedSet A} `{Galois A B} : Prop :=
  preorder_sound : ∀ x y : A, x ⊑ y → γ x ⊆ γ y.

Ltac pre_trans :=
  match goal with
  | H : ?a ⊑ ?b, K : ?b ⊑ ?c  |- ?a ⊑ ?c =>
      eapply preorder_trans; [apply H|assumption]
  end.

Ltac proof_preorder R := 
  split with (preorder:=R); autounfold with preorders;
  [> intros x; (destruct x; eauto with preorders) + 
               (constructor;intros; apply preorder_refl + assumption)| 
     intros x y z Hxy Hyz; (destruct x, y, z + constructor;intros);
     eauto with preorders; inversion Hxy; inversion Hyz; eauto with preorders ].

Inductive bot_le {A} `{PreorderedSet A} : (A+⊥) → (A+⊥) → Prop :=
  | bot_le_l : ∀ y, bot_le Bot y
  | bot_le_not : ∀ x y, x ⊑ y → bot_le (NotBot x) (NotBot y).
Hint Constructors bot_le : preorders.

Instance preorder_bot {A} `{PreorderedSet A} : PreorderedSet (A+⊥).
Proof.
  proof_preorder bot_le.
Defined.

Inductive top_le {A} `{PreorderedSet A} : (A+⊤) → (A+⊤) → Prop :=
  | top_le_r : ∀ x, top_le x Top 
  | top_le_not : ∀ x y, x ⊑ y → top_le (NotTop x) (NotTop y).
Hint Constructors top_le : preorders.

Instance preorder_top {A} `{PreorderedSet A} : PreorderedSet (A+⊤).
Proof. proof_preorder top_le. Defined.

Section preordered_functions.
  Context {A A' : Type} `{A_preorder : PreorderedSet A'}.

  Inductive pointwise_ordering : (A → A') → (A → A') → Prop :=
  | pointwise_cons : ∀ f g,  
      (∀ x, preorder (f x) (g x)) → pointwise_ordering f g.
  Hint Constructors pointwise_ordering : preorders.

  Global Instance preordered_function_spaces : PreorderedSet (A->A').
  Proof. proof_preorder pointwise_ordering. Defined.
End preordered_functions.
Hint Constructors pointwise_ordering : soundness.

Section preordered_pairs.
  Context {A B : Type} 
    `{A_preorder : PreorderedSet A, B_preorder : PreorderedSet B}.

  Inductive preorder_pair_le : prod A B → prod A B → Prop :=
    | preorder_pair_cons : ∀ a b c d,
        preorder a c → preorder b d → preorder_pair_le (a,b) (c,d).
  Hint Constructors preorder_pair_le : preorders.

  Global Instance preorder_pairs : PreorderedSet (A * B)%type.
  Proof.
    proof_preorder preorder_pair_le. 
  Defined.

  Lemma preorder_pair_spec : ∀ p q, ∃ a b c d,
    preorder p q <-> preorder (a, b) (c, d).
  Proof.
    intros. destruct p, q. exists a, b, a0, b0. reflexivity.
  Qed.
End preordered_pairs.
Hint Constructors preorder_pair_le : soundness.

Definition unit_le (u v : unit) : Prop := True.
Hint Unfold unit_le : preorders.

Instance preorder_unit : PreorderedSet unit.
Proof. proof_preorder unit_le. Defined.

Section preordered_sets_le.
  Context {A : Type}.

  Inductive preordered_set_le : (℘ A) → (℘ A) → Prop :=
    | preordered_set_le_cons : ∀ (s t : A → Prop),
        (∀ x, s x → t x) → preordered_set_le s t.
  Hint Constructors preordered_set_le : preorders.

  Global Instance types_to_prop : PreorderedSet (℘ A).
  Proof. proof_preorder preordered_set_le. Defined.

End preordered_sets_le.
Hint Constructors preordered_set_le : soundness.

Section identity_preorder.
  Context {A} `{A_preorder : PreorderedSet A}.

  Definition identity_le (i1 i2 : Identity A) : Prop :=
    match i1, i2 with
    | identity a1, identity a2 => preorder a1 a2
    end.
  Hint Unfold identity_le : preorders.

  Global Instance identity_preorder : PreorderedSet (Identity A).
  Proof. proof_preorder identity_le. Defined.
End identity_preorder.

Section option_preorder.
  Context {A} `{A_preorder : PreorderedSet A}.

  Inductive option_le : option A → option A → Prop :=
    | option_le_none : ∀ m, option_le m None
    | option_le_just : ∀ x y, preorder x y → option_le (Some x) (Some y).
  Hint Constructors option_le : preorders.

  Global Instance option_preorder : PreorderedSet (option A).
  Proof. proof_preorder option_le. Defined.
End option_preorder.
Hint Constructors option_le : soundness.

Global Instance preorder_nat : PreorderedSet nat.
Proof. proof_preorder le; eauto with arith. Defined.

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
Hint Constructors optionA_le : soundness.
