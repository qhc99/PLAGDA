module 747Quantifiers where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s) -- added ≤
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) -- added proj₂
open import Data.Sum using (_⊎_; inj₁; inj₂ ) -- added inj₁, inj₂
open import Function using (_∘_) -- added

-- Copied from 747Isomorphism.

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  constructor mk-≃  -- This has been added, not in PLFA
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

-- Logical forall is, not surpringly, ∀.
-- Forall elimination is also function application.

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- In fact, A → B is nicer syntax for ∀ (_ : A) → B.

-- 747/PLFA exercise: ForAllDistProd (1 point)
-- Show that ∀ distributes over ×.
-- (The special case of → distributes over × was shown in the Connectives chapter.)

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× {A} {B} {C} = mk-≃ ∀-distrib-×-to ∀-distrib-×-from ∀-distrib-×-from∘to ∀-distrib-×-to∘from
  where
    {--
    Refine two times to pattern match lambda and operator "_×_".
    Refine on the two holes.
    The first hole: goal "B x₁", context "x₁ : A" "x : (x₂ : A) → B x₂ × C x₂".
    We apply "x" to "x₁" to get "B x₁ × C x₁", then we use "proj₁" to get the goal from the result.
    The second hole has similar idea.
    --}
    ∀-distrib-×-to : ((x : A) → B x × C x) → ((x : A) → B x) × ((x : A) → C x)
    ∀-distrib-×-to = λ x → ⟨ (λ x₁ → proj₁ (x x₁)) , (λ x₁ → proj₂ (x x₁)) ⟩

    {--
    Case split on null, we find there is a variable which contain a "_×_".
    So we use pattern match on this variable.
    Then context "x₁ : A
                  f2 : (x : A) → C x
                  f1 : (x : A) → B x"
    and goal: "B x₁ × C x₁".
    It is clear that we can use "f1" and "f2" to get "B x₁" and "C x₁", then apply constructor to them.
    --}
    ∀-distrib-×-from : ((x : A) → B x) × ((x : A) → C x) → (x : A) → B x × C x
    ∀-distrib-×-from ⟨ f1 , f2 ⟩  x₁ = ⟨ f1 x₁ , f2 x₁ ⟩

    {--
    Refine on the hole get refl.
    --}
    ∀-distrib-×-from∘to : (x : (x₁ : A) → B x₁ × C x₁) → 
                          (∀-distrib-×-from ∘ ∀-distrib-×-to) x ≡ x
    ∀-distrib-×-from∘to fb×c = refl

    {--
    Refine on the hole get refl.
    --}
    ∀-distrib-×-to∘from : (y : ((x : A) → B x) × ((x : A) → C x)) →
                          (∀-distrib-×-to ∘ ∀-distrib-×-from) y ≡ y
    ∀-distrib-×-to∘from f×g = refl

-- 747/PLFA exercise: SumForAllImpForAllSum (1 point)
-- Show that a disjunction of foralls implies a forall of disjunctions.

{--
Input has "_⊎_", so we case split it and get two cases.
For the first hole, we get lambda expression after refine. The goal is "B x₁ ⊎ C x₁", context "x₁ : A", "x : (x₂ : A) → B x₂".
We get "B x₁" by apply "x" to "x₁", then use "inj₁" to construct the goal.
The second case has similar idea.
--}
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ x) = λ x₁ → inj₁ (x x₁)
⊎∀-implies-∀⊎ (inj₂ y) = λ x → inj₂ (y x)

-- Existential quantification can be defined as a pair:
-- a witness and a proof that the witness satisfies the property.

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- Some convenient syntax.

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- Unfortunately, we can use the RHS syntax in code,
-- but the LHS will show up in displays of goal and context.

-- This is equivalent to defining a dependent record type.

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

-- By convention, the library uses ∃ when the domain of the bound variable is implicit.

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

-- More special syntax.

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Above we saw two ways of constructing an existential.
-- We eliminate an existential with a function that consumes the
-- witness and proof and reaches a conclusion C.

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , x₁ ⟩ = f x x₁

-- This is a generalization of currying (from Connectives).
-- currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = 
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- 747/PLFA exercise: ExistsDistSum (2 points)
-- Show that existentials distribute over disjunction.

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = {!!}

-- 747/PLFA exercise: ExistsProdImpProdExists (1 point)
-- Show that existentials distribute over ×.

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ = {!!}

-- An existential example: revisiting even/odd.

-- Recall the mutually-recursive definitions of even and odd.

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- An number is even iff it is double some other number.
-- A number is odd iff is one plus double some other number.
-- Proofs below.

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ e = {!!}
odd-∃ e = {!!}

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even e = {!!}
∃-odd  e = {!!}

-- PLFA exercise: what if we write the arithmetic more "naturally"?
-- (Proof gets harder but is still doable).

-- 747/PLFA exercise: AltLE (3 points)
-- An alternate definition of y ≤ z.
-- (Optional exercise: Is this an isomorphism?)

∃-≤ : ∀ {y z : ℕ} → ( (y ≤ z) ⇔ ( ∃[ x ] (y + x ≡ z) ) )
∃-≤ = {!!}

-- The negation of an existential is isomorphic to a universal of a negation.

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = {!!}

-- 747/PLFA exercise: ExistsNegImpNegForAll (1 point)
-- Existence of negation implies negation of universal.

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ∃¬B = {!!}

-- The converse cannot be proved in intuitionistic logic.

-- PLFA exercise: isomorphism between naturals and existence of canonical binary.
-- This is essentially what we did at the end of 747Isomorphism.