Require Export Base.
Require Import Classes.Applicative.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.

Implicit Type M : Type → Type.
Implicit Type A : Type.

Class MonadExcept M `{MonadFail M} A := {
  catch : M A -> M A -> M A;
  catch_left : ∀ (x : M A), catch fail x = x;
  catch_right : ∀ (x : M A), catch x fail = x;
  catch_assoc : ∀ (x y z: M A),
    catch x (catch y z) = catch (catch x y) z;
  catch_pure : ∀ (x : M A) (a : A),
    catch (pure a) x = pure a;
}.
Arguments catch : simpl never.

Hint Rewrite @catch_left @catch_right @catch_pure : soundness.
