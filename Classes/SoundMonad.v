Require Export Base.
Require Import Classes.PreorderedSet.
Require Import Classes.Galois.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Instances.Galois.

Section sound_monad.
  Context (M M' : Type → Type) `{M_fail : MonadFail M, M'_fail : MonadFail M'}.
  Context {M_preorder : ∀ T', PreorderedSet T' → PreorderedSet (M' T')}.
  Context {M_galois : ∀ T T' {HT : PreorderedSet T'}, Galois T T' → Galois (M T) (M' T')}.

  Class SoundMonad : Type :=
  {
    return_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (returnM (M:=M') (A:=A')) (returnM (M:=M) (A:=A));
    bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (M:=M') (A:=A') (B:=B')) (bindM (M:=M) (A:=A) (B:=B));
    gamma_fail : ∀ (A A' : Type) `{Galois A A'} (m : M A), gamma fail m;
  }.
End sound_monad.
Hint Resolve return_sound bind_sound gamma_fail : soundness.
