Require Export Base Coq.Strings.String.
Require Import Classes.Monad.
Require Import Classes.Galois.

Class MonadState (S : Type) (M : Type -> Type) {MM : Monad M} :=
{
  get : M S;
  put : S -> M unit;
}.

Class get_state_sound (M M' : Type → Type) {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A' : Type, Galois A A' → Galois (M A) (M' A')}
  {S S' : Type} {GS : Galois S S'}  {MS : MonadState S M}
  {MS' : MonadState S' M'} : Prop := get_sound : γ get get.

Class put_state_sound (M M' : Type → Type) {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A' : Type, Galois A A' → Galois (M A) (M' A')}
  {S S' : Type} {GS : Galois S S'}  {MS : MonadState S M}
  {MS' : MonadState S' M'} : Prop := put_sound : ∀ s s', γ s s' → γ (put s) (put s').
