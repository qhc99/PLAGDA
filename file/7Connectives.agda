module 747Connectives where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)

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

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_ 

-- You may copy over the various reasoning modules if you wish.

-- End of code from 747Isomorphism.

-- Logical AND is Cartesian product.

data _×_ (A : Set) (B : Set) : Set where

  ⟨_,_⟩ : 
      A
    → B
      -----
    → A × B

-- Destructors (eliminators) for ×.

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A

proj₁ ⟨ x , x₁ ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B

proj₂ ⟨ x , x₁ ⟩ = x₁

-- An easier (equivalent) construction using records.

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

-- Eta-equivalence relates constructors and destructors.

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , x₁ ⟩ = refl

-- Bool (Booleans), a type with exactly two members.

infixr 2 _×_
data Bool : Set where
  true  : Bool
  false : Bool

-- A type with three members (useful for examples).

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- Bool × Tri has six members.
-- Here is a function counting them.

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

-- Cartesian product is commutative and associative up to isomorphism.

×-comm : ∀ {A B : Set} → A × B ≃ B × A
to ×-comm ⟨ x , x₁ ⟩ = ⟨ x₁ , x ⟩
from ×-comm ⟨ x , x₁ ⟩ = ⟨ x₁ , x ⟩
from∘to ×-comm ⟨ x , x₁ ⟩ = refl
to∘from ×-comm ⟨ x , x₁ ⟩ = refl

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
to ×-assoc ⟨ ⟨ x₁ , x₂ ⟩ , x ⟩ = ⟨ x₁ , ⟨ x₂ , x ⟩ ⟩
from ×-assoc ⟨ x , ⟨ x₁ , x₂ ⟩ ⟩ = ⟨ ⟨ x , x₁ ⟩ , x₂ ⟩
from∘to ×-assoc ⟨ ⟨ x₁ , x₂ ⟩ , x ⟩ = refl
to∘from ×-assoc ⟨ x , ⟨ x₁ , x₂ ⟩ ⟩ = refl

-- 747/PLFA exercise: IffIsoIfOnlyIf (1 point)
-- Show A ⇔ B is isomorphic to (A → B) × (B → A).
{- 
The First case: 
Case split on null, then case split on variable "x", we have goal "(A → B) × (B → A)", and context "to : A → B" and "from : B → A",
Then we just construct the goal using operator "⟨_,_⟩".

The Second case:
It is the inverse of the first case, basically we can copy, paste and invert order of input and output of the first case.

The Third case and fourth case:
Case split two times. 
The goal of thrid case is not obviously refl, but after refine it becomes refl.
The goal of fourth case is obviously refl.
-}

iff-iso-if-onlyif : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
_≃_.to iff-iso-if-onlyif record { to = to ; from = from } = ⟨ to , from ⟩
from iff-iso-if-onlyif ⟨ x , x₁ ⟩ = record { to = x ; from = x₁ }
from∘to iff-iso-if-onlyif record { to = to ; from = from } = refl
to∘from iff-iso-if-onlyif ⟨ x , x₁ ⟩ = refl

-- Logical True is a type with one member (unit)

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

-- Unit is the left and right identity of product.

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
to ⊤-identityˡ = proj₂
from ⊤-identityˡ = λ a → ⟨ tt , a ⟩
from∘to ⊤-identityˡ ⟨ w , a ⟩  = cong (λ z → ⟨ z , a ⟩ ) (η-⊤ w)
to∘from ⊤-identityˡ = λ _ → refl

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ = 
  mk-≃ 
    proj₁ 
    (λ a → ⟨ a , tt ⟩) 
    (λ { ⟨ a , w ⟩ → cong (λ z → ⟨ a , z ⟩) (η-⊤ w) }) 
    λ _ → refl

-- Logical OR (disjunction) is sum (disjoint union).

data _⊎_ : Set → Set → Set where

  inj₁ : ∀ {A B : Set}
    → A
      -----
    → A ⊎ B

  inj₂ : ∀ {A B : Set}
    → B
      -----
    → A ⊎ B

-- One way to eliminate a sum.

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ x) = g x

-- We typically use pattern-matching to eliminate sums.

-- Eta equivalence for sums.

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

-- A generalization.

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infix 1 _⊎_

-- Bool ⊎ Tri has five members

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

-- 747/PLFA exercise: SumCommIso (1 point)
-- Sum is commutative up to isomorphism.
{-
Case split on every possible variable until no variable contain "⊎".
Then from context the goal is very easy to prove.
-}
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
to ⊎-comm (inj₁ x) = inj₂ x
to ⊎-comm (inj₂ x) = inj₁ x
from ⊎-comm (inj₁ x) = inj₂ x
from ⊎-comm (inj₂ x) = inj₁ x
from∘to ⊎-comm (inj₁ x) = refl
from∘to ⊎-comm (inj₂ x) = refl
to∘from ⊎-comm (inj₁ x) = refl
to∘from ⊎-comm (inj₂ x) = refl


-- 747/PLFA exercise: SumAssocIso (1 point)
-- Sum is associative up to isomorphism.
{-
We case split until no variable contain "_⊎_".

"to" and "from" of isomorphism are solved by using "inj" according to the variable's position in the goal, basically if 
the variable appear in the first term of "⊎" in the goal, we use "inj₁". Otherwise we use "inj₂".

"to∘from" and "from∘to" of isomorphism become refl when case split to ends.
-}
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
to ⊎-assoc (inj₁ (inj₁ x)) = inj₁ x
to ⊎-assoc (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
to ⊎-assoc (inj₂ x) = inj₂ (inj₂ x)
from ⊎-assoc (inj₁ x) = inj₁ (inj₁ x)
from ⊎-assoc (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
from ⊎-assoc (inj₂ (inj₂ x)) = inj₂ x
from∘to ⊎-assoc (inj₁ (inj₁ x)) = refl
from∘to ⊎-assoc (inj₁ (inj₂ x)) = refl
from∘to ⊎-assoc (inj₂ x) = refl
to∘from ⊎-assoc (inj₁ x) = refl
to∘from ⊎-assoc (inj₂ (inj₁ x)) = refl
to∘from ⊎-assoc (inj₂ (inj₂ x)) = refl


-- Logical False is the empty type ("bottom", "empty").

data ⊥ : Set where
  -- no clauses!

-- Ex falso quodlibet "from falsehood, anything follows".

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A

⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- 747/PLFA exercise: EmptyLeftIdSumIso (1 point)
-- Empty is the left unit of sum up to isomorphism.
{-
Case split consecutively until it is very easy to prove.
-}
⊎-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
to ⊎-identityˡ (inj₂ x) = x
from ⊎-identityˡ x = inj₂ x
from∘to ⊎-identityˡ (inj₂ x) = refl
to∘from ⊎-identityˡ y = refl

-- 747/PLFA exercise: EmptyRightIdSumIso (1 point)
-- Empty is the right unit of sum up to isomorphism.
{-
Same idea as the exercise above.
-}
⊎-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
to ⊎-identityʳ (inj₁ x) = x
from ⊎-identityʳ x = inj₁ x
from∘to ⊎-identityʳ (inj₁ x) = refl
to∘from ⊎-identityʳ = λ _ → refl

-- Logical implication (if-then) is... the function type constructor!
-- Eliminating an if-then (modus ponens) is function application.

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B

→-elim L M = L M

-- This works because eta-reduction for → is built in.

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

-- The function space A → B is sometimes called the exponential Bᴬ.
-- Bool → Tri has 3² or 9 members.

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

-- In math,   (p ^ n) ^ m = p ^ (n * m).
-- For types, (A ^ B) ^ C ≃ A ^ (B × C).

-- In a language where functions take multiple parameters,
-- this is called "currying".

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
to currying f ⟨ a , b ⟩ = f a b
from currying f a b = f ⟨ a , b ⟩
from∘to currying x = refl
to∘from currying y = extensionality (λ { ⟨ a , b ⟩ → refl})

-- In math,   p ^ (n + m) = (p ^ n) * (p ^ m).
-- For types, (A ⊎ B → C) ≃ ((A → C) × (B → C)).

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
to →-distrib-⊎ x = ⟨ (λ x₁ → x (inj₁ x₁)) , (λ x₁ → x (inj₂ x₁)) ⟩
from →-distrib-⊎ ⟨ x , x₁ ⟩ (inj₁ x₂) = x x₂
from →-distrib-⊎ ⟨ x , x₁ ⟩ (inj₂ x₂) = x₁ x₂
from∘to →-distrib-⊎ x = extensionality λ { (inj₁ x) → refl ; (inj₂ x) → refl }
to∘from →-distrib-⊎ ⟨ x , x₁ ⟩ = refl

-- In math,   (p * n) ^ m = (p ^ m) * (n ^ m).
-- For types, (A → B × C) ≃ (A → B) × (A → C).

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
to →-distrib-× x = ⟨ (λ x₁ → proj₁ (x x₁)) , (λ x₁ → proj₂ (x x₁)) ⟩
from →-distrib-× ⟨ x , x₁ ⟩ = λ x₂ → ⟨ (x x₂) , (x₁ x₂) ⟩
from∘to →-distrib-× f = extensionality λ x → η-× (f x)
to∘from →-distrib-× ⟨ x , x₁ ⟩ = refl

-- More distributive laws.

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
to ×-distrib-⊎ ⟨ inj₁ x , x₁ ⟩ = inj₁ ⟨ x , x₁ ⟩
to ×-distrib-⊎ ⟨ inj₂ x , x₁ ⟩ = inj₂ ⟨ x , x₁ ⟩
from ×-distrib-⊎ (inj₁ ⟨ x , x₁ ⟩) = ⟨ (inj₁ x) , x₁ ⟩
from ×-distrib-⊎ (inj₂ ⟨ x , x₁ ⟩) = ⟨ (inj₂ x) , x₁ ⟩
from∘to ×-distrib-⊎ ⟨ inj₁ x , x₁ ⟩ = refl
from∘to ×-distrib-⊎ ⟨ inj₂ x , x₁ ⟩ = refl
to∘from ×-distrib-⊎ (inj₁ ⟨ x , x₁ ⟩) = refl
to∘from ×-distrib-⊎ (inj₂ ⟨ x , x₁ ⟩) = refl

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
_≲_.to ⊎-distrib-× (inj₁ ⟨ x , x₁ ⟩) = ⟨ (inj₁ x) , (inj₁ x₁) ⟩
_≲_.to ⊎-distrib-× (inj₂ x) = ⟨ (inj₂ x) , (inj₂ x) ⟩
_≲_.from ⊎-distrib-× ⟨ inj₁ x , inj₁ x₁ ⟩ = inj₁ ⟨ x , x₁ ⟩
_≲_.from ⊎-distrib-× ⟨ inj₁ x , inj₂ x₁ ⟩ = inj₂ x₁
_≲_.from ⊎-distrib-× ⟨ inj₂ x , x₁ ⟩ = inj₂ x
_≲_.from∘to ⊎-distrib-× (inj₁ ⟨ x , x₁ ⟩) = refl 
_≲_.from∘to ⊎-distrib-× (inj₂ x) = refl

-- Think of a counterexample to show the above isn't an isomorphism.

-- PLFA exercise: a weak distributive law.
{-
For the first case, we have "A" and "C", then using "inj₁" on "A", we get "A ⊎ (B × C)".
For the second case, we have "B" and "C", then we have "B × C" and finally the goal by "inj₂".
-}
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , x₁ ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , x₁ ⟩ = inj₂ ⟨ x , x₁ ⟩
-- State and prove the strong law, and explain the relationship.

-- 747/PLFA exercise: SumOfProdImpProdOfSum (1 point)
-- A disjunct of conjuncts implies a conjunct of disjuncts.
{-
Case split and pattern matching, then reconstruct according to context and variable position, which 
is used to determine which injunction to use.

In the first case, we have "A × B", which means "A and B". Then we can get "A ⊎ C" by "inj₁" and "B ⊍ D" using similar idea.
The second case has the same idea as the first case.
-}
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- PLFA exercise: Is the converse true? If so, prove it; if not, give a counterexample.
{-
For the case we have "A" and "D" to construct "A ⊎ C" and "B ⊎ D", we cannot build the goal since "_×_" requires 
the knowledge of "B" and "C", which we do not have.

converse-⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
converse-⊎×-implies-×⊎ ⟨ inj₁ x , inj₁ x₁ ⟩ = inj₁ ⟨ x , x₁ ⟩
converse-⊎×-implies-×⊎ ⟨ inj₁ x , inj₂ x₁ ⟩ = {!   !}
converse-⊎×-implies-×⊎ ⟨ inj₂ x , inj₁ x₁ ⟩ = {!   !}
converse-⊎×-implies-×⊎ ⟨ inj₂ x , inj₂ x₁ ⟩ = inj₂ ⟨ x , x₁ ⟩
-}

-- See PLFA for a number of slight differences with the standard library.

-- Unicode introduced in this chapter:

{-

  ×  U+00D7  MULTIPLICATION SIGN (\x)
  ⊎  U+228E  MULTISET UNION (\u+)
  ⊤  U+22A4  DOWN TACK (\top)
  ⊥  U+22A5  UP TACK (\bot)
  η  U+03B7  GREEK SMALL LETTER ETA (\eta)
  ₁  U+2081  SUBSCRIPT ONE (\_1)
  ₂  U+2082  SUBSCRIPT TWO (\_2)
  ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>, \iff, \lr=)

-}