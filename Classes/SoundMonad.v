Require Export Base.
Require Import Classes.Monad.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.Galois.
Require Import Instances.Galois.

Section monad_sound. 
  Context (M M' : Type → Type) `{Monad M, Monad M'}.
  Context {A A' B B' : Type} `{Galois A A', Galois B B'}.
  Context `{Galois (M A) (M' A'), Galois (M B) (M' B')}.
  Context `{Galois (M (A → B)) (M' (A' → B'))}.

  Class SoundMonads : Type :=
  {
    fmap_sound : gamma (B:=(A' → B') → M' A' → M' B')
                  fmap fmap;
    pure_sound : gamma (B:=A' → M' A') pure pure;
    app_sound  : gamma (B:=M' (A' → B') → M' A' → M' B')
                  app app; 
    bind_sound : gamma (B:=M' A' → (A' → M' B') → M' B')
                  bindM bindM;
  }.
End monad_sound.
Hint Resolve fmap_sound pure_sound app_sound bind_sound : soundness.
