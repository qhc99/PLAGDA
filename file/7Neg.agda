module 747Negation where

-- Library

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong) -- added last
open import Data.Nat using (ℕ; zero; suc) 
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂)


-- Negation is defined as implying false.

¬_ : Set → Set
¬ A = A → ⊥

-- if both ¬ A and A hold, then ⊥ holds (not surprisingly).

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥

¬-elim ¬a a = ¬a a

infix 3 ¬_

-- Double negation introduction.

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A

¬¬-intro a ¬a = ¬a a

-- Double negation cannot be eliminated in intuitionistic logic.

-- Triple negation elimination.

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A

¬¬¬-elim ¬¬¬a a = ¬¬¬a (¬¬-intro a)

-- One direction of the contrapositive.

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)

contraposition a→b ¬b a = ¬b (a→b a)

-- The other direction cannot be proved in intuitionistic logic.

-- not-equal-to.

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

-- One of the first-order Peano axioms.

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

-- Copied from 747Isomorphism.

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Two proofs of ⊥ → ⊥ which look different but are the same
-- (assuming extensionality).
   
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

-- Assuming extensionality, any two proofs of a negation are the same

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

-- Strict inequality (copied from 747Relations).

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- 747/PLFA exercise: NotFourLTThree (1 point)
-- Show ¬ (4 < 3).
{-
Case split on null, then case split on variable consecutively until it is absurd.
-}
¬4<3 : ¬ (4 < 3)
¬4<3 (s<s (s<s (s<s ())))

-- 747/PLFA exercise: LTIrrefl (1 point)
-- < is irreflexive (never reflexive).
{-
Case split both on "n" and "x".
By induction, we input "¬n<n n" and refine, find its context is: "x : n < n" and goal "n < n", then we got the answer.
-}
¬n<n : ∀ (n : ℕ) → ¬ n < n
¬n<n zero ()
¬n<n (suc n) (s<s x) = ¬n<n n x

-- 747/PLFA exercise: LTTrich (3 points)
-- Show that strict inequality satisfies trichotomy,
-- in the sense that exactly one of the three possibilities holds.
-- Here is the expanded definition of trichotomy.

data Trichotomy (m n : ℕ) : Set where
  is-< : m < n → ¬ m ≡ n → ¬ n < m → Trichotomy m n
  is-≡ : m ≡ n → ¬ m < n → ¬ n < m → Trichotomy m n
  is-> : n < m → ¬ m ≡ n → ¬ m < n → Trichotomy m n

{-
Three trivial helper function.
-}
suc-¬-< : ∀ {m n : ℕ} → ¬ m < n → ¬ (suc m) < (suc n)
suc-¬-< x (s<s x₁) = x x₁

suc-¬-≡ : ∀ {m n : ℕ} → ¬ m ≡ n → ¬ (suc m) ≡ (suc n)
suc-¬-≡ x refl = x refl

suc-≡ : ∀ {m n : ℕ} → m ≡ n → (suc m) ≡ (suc n)
suc-≡ refl = refl

{-
Basically we need to prove that relation still hold when suc on both sides. 
Thus we set three trivial helper function above.
-}
suc-<-trichotomy : ∀ {m n : ℕ} → Trichotomy m n → Trichotomy (suc m) (suc n)
suc-<-trichotomy (is-< x x₁ x₂) = is-< (s<s x) (suc-¬-≡ x₁) (suc-¬-< x₂)
suc-<-trichotomy (is-≡ x x₁ x₂) = is-≡ (suc-≡ x) (suc-¬-< x₁) (suc-¬-< x₂)
suc-<-trichotomy (is-> x x₁ x₂) = is-> (s<s x) (suc-¬-≡ x₁) (suc-¬-< x₂)

{-
Case split both on "m" and "n", the first three cases is trivial since they can be solved by C-c C-a.
With the experience of trichotomy exercise before, we set "suc-<-trichotomy" helper function above.
-}
<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = is-≡ refl (λ ()) (λ ())
<-trichotomy zero (suc n) = is-< z<s (λ ()) (λ ())
<-trichotomy (suc m) zero = is-> z<s (λ ()) (λ ())
<-trichotomy (suc m) (suc n) = suc-<-trichotomy (<-trichotomy m n)

-- PLFA exercise: one of DeMorgan's Laws as isomorphism
--⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
-- Expand negation as implies-false, then look in 747Relations
-- for a law of which this is a special case.

open import plfa.part1.Isomorphism using (_≃_)
open import plfa.part1.Isomorphism using (_∘_)

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ x) = g x

{-
The "to" case: case split on null then refine, we get two holes seperated by the "," operator of the long module name.
Two goals of two holes are function type. Refine on the first hole, we get goal "⊥" and context "x₁ : A" "x : ¬ (A ⊎ B)".
By "inj₁" we have "A ⊎ B", then apply "x" to the result we get the goal. The second hole has similar idea.

Refine the "from" case, we have context "x : ¬ A × ¬ B" "x₁ : A ⊎ B" and goal "⊥", by "proj" we have "¬ A" and "¬ B"
from "x", which can be written as "A → ⊥" and "B → ⊥". These are the first two argument of "case-⊎", and "x₁" is 
the third argument, output is exactly the goal, then we get the answer.

In the "from∘to" case, "x" is a function. The goal is equality on function, so we need extensionality. After refine,
the goal is a function, so we refine again to get a lambda expression. The input of this lambda expression is type "⊎",
which needs case split. There we should use pattern matching of lambda for case split. After pattern matching, 
all cases here become refl.

"to∘from" case: case split on null then case split on the only variable, the goal is refl.
-}
⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = 
  record  { 
          to = ⊎-dual-×-to ; 
          from = ⊎-dual-×-from ; 
          from∘to = ⊎-dual-×-from∘to ; 
          to∘from = ⊎-dual-×-to∘from
          }
  where
    ⊎-dual-×-to : ¬ (A ⊎ B) → ¬ A × ¬ B
    ⊎-dual-×-to x = (λ x₁ → x (inj₁ x₁)) Data.Product., λ x₁ → x (inj₂ x₁)

    ⊎-dual-×-from : ¬ A × ¬ B → ¬ (A ⊎ B)
    ⊎-dual-×-from  = λ x x₁ → case-⊎ (proj₁ x) (proj₂ x) x₁

    ⊎-dual-×-from∘to : ∀ (x : ¬ (A ⊎ B)) → (⊎-dual-×-from ∘ ⊎-dual-×-to) x ≡ x
    ⊎-dual-×-from∘to x = extensionality λ { (inj₁ y) → refl
                                            ; (inj₂ y) → refl
                                            }

    ⊎-dual-×-to∘from : ∀ (y : ¬ A × ¬ B) → ⊎-dual-×-to (⊎-dual-×-from y) ≡ y
    ⊎-dual-×-to∘from (fst Data.Product., snd) = refl

-- What about ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)?
-- Answer: RHS implies LHS but converse cannot be proved in intuitionistic logic.


-- Intuitionistic vs classical logic.

-- The law of the excluded middle (LEM, or just em) cannot be
-- proved in intuitionistic logic.
-- But we can add it, and get classical logic.

--postulate
--  em : ∀ {A : Set} → A ⊎ ¬ A

-- How do we know this does not give a contradiction?
-- The following theorem of intuitionistic logic demonstrates this.
-- (The proof is compact, but takes some thought.)

-- 747 exercise: excluded middle is irrefutable (2 points, not 2021)

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable f = f (inj₂ (λ x → f (inj₁ x))) --!!!

-- PLFA exercise: classical equivalences
-- Excluded middle cannot be proved in intuitionistic logic,
-- but adding it is consistent and gives classical logic.
-- Here are four other classical theorems with the same property.
-- You can show that each of them is logically equivalent to all the others.
-- You do not need to prove twenty implications, since implication is transitive.
-- But there is a lot of choice as to how to proceed!

-- Excluded Middle
em = ∀ {A : Set} → A ⊎ ¬ A

-- Double Negation Elimination
dne = ∀ {A : Set} → ¬ ¬ A → A

-- Peirce’s Law
peirce =  ∀ {A B : Set} → ((A → B) → A) → A

-- Implication as disjunction
iad =  ∀ {A B : Set} → (A → B) → ¬ A ⊎ B

-- De Morgan:
dem = ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

-- End of classical five exercise.

-- Definition: a formula is stable if double negation holds for it.

Stable : Set → Set
Stable A = ¬ ¬ A → A

-- PLFA exercise: every negated formula is stable.
-- This is triple negation elimination.
{-
By the goal and context, we should use "¬¬¬-elim".
-}
∀-¬-is-Stable : ∀{A : Set} → Stable (¬ A)
∀-¬-is-Stable x x₁ = (¬¬¬-elim x) x₁

-- PLFA exercise: the conjunction of two stable formulas is stable.
-- This is the version of DeMorgan's Law that is a special case, above.

postulate
  dne′ : ∀ {A : Set} → ¬ ¬ A → A
{-
By the goal and context, we should use "dne", which is postulated above.
-}
×-Stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-Stable sa sb = λ x → dne′ x


-- Where negation sits in the standard library.

import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)

-- Unicode used in this chapter:

{-

  ¬  U+00AC  NOT SIGN (\neg)
  ≢  U+2262  NOT IDENTICAL TO (\==n)

-}