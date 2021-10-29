module 747Properties where

open import PropertiesRefactor
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Agda.Builtin.Bool using (true; false)
open import Function using (_∘_)
open import LambdaDefs

-- 747/PLFA exercise: AltProg (5 points)
-- Here is an alternate formulation of progress.
-- Show that it is isomorphic to Progress M, and prove this form
-- of the progress theorem directly.

progress-iso : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
progress-iso {M} = mk-≃ progress-iso-to progress-iso-from progress-iso-from∘to progress-iso-to∘form
  where
  {-
  Case split.
  For function "step", we need to specify its implicit argument since it is very very very useful...
  Basically we need to decide which inj to use by the idea of "V¬—→" and "—→¬V" above.
  -}
  progress-iso-to :  ∀ {P} → Progress P → Value P ⊎ ∃-syntax (_—→_ P)
  progress-iso-to (step {n} x) = inj₂ ⟨ n , x ⟩
  progress-iso-to (done x) = inj₁ x

  {-
  Case split "_⊎_".
  In the first case we have "Value M", so we should refine on "done".
  In the second case, since we do not have "Value M", the only remain option is "step".
  -}
  progress-iso-from : Value M ⊎ ∃-syntax (_—→_ M) → Progress M
  progress-iso-from (inj₁ x) = done x
  progress-iso-from (inj₂ ⟨ fst , snd ⟩) = step snd

 {-compute on goal get refl.-}
  progress-iso-from∘to : (x : Progress M) → progress-iso-from (progress-iso-to x) ≡ x
  progress-iso-from∘to (step x) = refl
  progress-iso-from∘to (done x) = refl

  {-for the second case, refine get refl.-}
  progress-iso-to∘form : (y : Value M ⊎ ∃-syntax (_—→_ M)) → progress-iso-to (progress-iso-from y) ≡ y
  progress-iso-to∘form (inj₁ x) = refl
  progress-iso-to∘form (inj₂ y) = refl

{-Since we know "Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)"-}
progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ M x = (_≃_.to progress-iso) (progress x)

-- 747/PLFA exercise: ValueEh (1 point)
-- Write a function to decide whether a well-typed term is a value.
-- Hint: reuse theorems proved above to do most of the work.

{-we know there is a progress, so we use with clause there. Then it becomes easy to prove.-}
value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? x with progress x 
... | step x₁ = no (—→¬V  x₁)
... | done x₁ = yes x₁


-- 747/PLFA exercise: Unstuck (3 points)
-- Using progress and preservation, prove the following:
{-
The two constructors of "Progress" make one component of "Stuck" produce the evidence of "⊥".
We use "with" and "progress m:a " to get "Progress" and to case split.
-}
unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck m:a ⟨ n , ¬v ⟩ with progress m:a 
... | step x = n x
... | done x = ¬v x

{-
Induction on the "M —↠ N", every recursion reduce one step "_—→_".
By "preserve m:a x" we get evidence of "M₁ —↠ N", which is second argument of recursion.
-}
preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves m:a (_ ∎) = m:a
preserves m:a (_ —→⟨ x ⟩ msn) = preserves (preserve m:a x) msn

{-
To get "¬ (Stuck N)" from "unstuck", we need "∅ ⊢ N ⦂ A", which can be built by "preserves".
Then we got the answer.
-}
wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs m:a msn = unstuck (preserves m:a msn)