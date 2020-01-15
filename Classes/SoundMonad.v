Require Export Base.
Require Import Classes.Monad.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.Galois.
Require Import Instances.Galois.

Section monad_sound. 
  Context M M' `{Monad M, Monad M'}.
  Context {M_galois : ∀ A A' : Type, Galois A A' → Galois (M A) (M' A')}.

  Class SoundMonad : Type := {
    fmap_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'}, 
      gamma (B:=(A' → B') → M' A' → M' B') fmap fmap;
    pure_sound : ∀ (A A': Type) `{Galois A A'},
      gamma (B:= (A' → M' A')) pure pure;
    app_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'}, 
      gamma (B:=M' (A' → B') → M' A' → M' B') app app;
    bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (B:=M' A' → (A' → M' B') → M' B') bindM bindM;
  }.
End monad_sound.
Hint Resolve fmap_sound pure_sound app_sound bind_sound : soundness.
