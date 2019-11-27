Require Export Base.
Require Import Classes.Monad.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.Galois.
Require Import Instances.Monad.
Require Import Instances.Preorder.
Require Import Instances.Galois.

Section monad_sound. 
  Context (M M' : Type → Type) `{Monad M, Monad M'}.
  Context {A A' B B' : Type} `{Galois A A', Galois B B'}.
  Context `{Galois (M A) (M' A'), Galois (M B) (M' B')}.
  Context `{Galois (M (A → B)) (M' (A' → B'))}.

  Class SoundMonads : Type :=
  {
    fmap_sound : gamma (fmap (Functor:=H2)) (fmap);
    pure_sound : gamma (pure (Applicative:=H3)) (pure);
    app_sound  : gamma (app (Applicative:=H3)) (app);
    bind_sound : gamma (bindM (Monad:=H4)) (bindM) ;
  }.
End monad_sound.
Hint Resolve fmap_sound pure_sound app_sound bind_sound : soundness.
