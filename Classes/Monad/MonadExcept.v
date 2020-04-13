Require Export Base.
Require Import Classes.Monad Classes.Joinable Classes.Galois.

Implicit Type M : Type → Type.
Implicit Type A : Type.

Class MonadExcept M {MM : Monad M} := {
  throw : ∀ {A}, M A;
  throw_left: ∀ {A B} (f : A → M B), throw >>= f = throw;
  catch : ∀ {A} {JA : Joinable A A} {JAI: JoinableIdem JA}, 
    M A -> M A -> M A;
  catch_left : ∀ {A} {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (x : M A), catch throw x = x;
  catch_right : ∀ {A} {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (x : M A), catch x throw = x;
  catch_return : ∀ {A} {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (x : M A) (a : A), catch (returnM a) x = returnM a;
}.
Arguments throw : simpl never.
Arguments catch : simpl never.
Hint Rewrite @throw_left @catch_left @catch_right @catch_return : monads.

Class MonadExceptSound (M M' : Type → Type) 
  {MM : Monad M} {MF : MonadExcept M}
  {MM' : Monad M'} {MF' : MonadExcept M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : Prop :=
  catch_sound : ∀ {A} {JA : Joinable A A} {JAI : JoinableIdem JA}
    {A'} {JA' : Joinable A' A'} {JAI' : JoinableIdem JA'}
    {GA : Galois A A'} 
    (p1 p2 : M A) (p1' p2' : M' A'),
    γ p1 p1' →
    γ p2 p2' → 
    γ (catch p1 p2) (catch p1' p2').

