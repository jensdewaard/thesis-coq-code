Require Export Base.
Require Import Classes.PreorderedSet.
Require Import Classes.Galois.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Instances.Galois.

Section sound_monad.
  Context (M M' : Type → Type) `{MonadFail M, MonadFail M'}.
  Context {M_preorder : ∀ T', PreorderedSet T' → PreorderedSet (M' T')}.
  Context {M_galois : ∀ T T' {HT : PreorderedSet T'}, Galois T T' → Galois (M T) (M' T')}.

  Class SoundMonad : Type :=
  {
    fmap_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (fmap (F:=M') (A:=A') (B:=B')) (fmap (F:=M) (A:=A) (B:=B));
    pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (F:=M') (A:=A')) (pure (F:=M) (A:=A));
    app_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (app (F:=M') (A:=A') (B:=B')) (app (F:=M) (A:=A) (B:=B));
    bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (M:=M') (A:=A') (B:=B')) (bindM (M:=M) (A:=A) (B:=B));
    gamma_fail : ∀ (A A' : Type) `{Galois A A'} (m : M A), gamma fail m;
  }.
End sound_monad.
Hint Resolve fmap_sound pure_sound app_sound bind_sound gamma_fail : soundness.
