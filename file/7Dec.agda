module 747Decidable where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym) -- added sym
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)


-- Copied from 747Isomorphism.

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

-- Copied from 747Relations.

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- Recall that the constructors for _≤_ are z≤n and s≤s.

-- Here are a couple of examples to show how to prove inequalities
-- (or their negations).

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

-- This should be familiar.

data Bool : Set where
  true  : Bool
  false : Bool

-- We can define a Boolean comparison function.

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

-- PLFA steps through these computations using equational reasoning.

_ : (2 ≤ᵇ 4) ≡ true
_ =  refl

_ : (4 ≤ᵇ 2) ≡ false
_ = refl

-- Relating evidence and computation.

T : Bool → Set
T true   =  ⊤
T false  =  ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true t = refl

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n t = z≤n
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

-- Getting the best of both worlds!

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

-- Helpers for defining _≤?_
-- If you don't use these, the examples below won't normalize.

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

-- Decidable ≤.

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
... | yes x = yes (s≤s x)
... | no x = no (¬s≤s x)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

-- We can also evaluate the LHS of these using C-c C-n.

-- 747/PLFA exercise: DecLT (3 point)
-- Decidable strict equality.
-- You will need these helper functions as we did above.
{--
Case split consecutivly.
--}
¬z<z : ¬ (zero < zero)
¬z<z ()

{--
Case split consecutivly., then answer becomes obvious.
--}
¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s x (s<s x₁) = x x₁

{--
Case split consecutivly.
--}
¬s<z : ∀ {n : ℕ} → ¬ (suc n < zero)
¬s<z ()

{--
Case split both on "m" and "n".
Although the first and the third case can be solved by C-c C-a, tests will not pass in this way.
We have hint of the three helper function and "_≤?_ ".
Thus we should solve the first and thrid case with the helper function.
For the fourth case, it is similar to "_≤?_", we add the "with" clause and correspoding variable, then split on it.
Using the "with" clause, the fourth case becomes easy to prove.
--}
_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no (¬z<z)
zero <? suc n = yes z<s
suc m <? zero = no (¬s<z)
suc m <? suc n with m <? n
... | yes x = yes (s<s x)
... | no x = no (λ x₁ → (¬s<s x)  x₁)

-- Some tests.

_ : 2 <? 4 ≡ yes (s<s (s<s (z<s)))
_ = refl

_ : 4 <? 2 ≡ no (¬s<s (¬s<s ¬s<z))
_ = refl

_ : 3 <? 3 ≡ no (¬s<s (¬s<s (¬s<s ¬z<z)))
_ = refl


-- 747/PLFA exercise: DecNatEq (3 points)
-- Decidable equality for natural numbers.
{-
The first three cases are trivial since they can be solved by C-c C-a.
For the fourth case, by the hint of previous exercise, here we use the "with" clause as before and add holes. 
The first hole can be solved by C-c C-a too, while for the second hole we need the rule "¬ (suc m) ≡ (suc n)", 
which is built by the nested helper function.
-}
_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n) -- split m,n
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no λ ()
suc m ≡ℕ? zero = no λ ()
suc m ≡ℕ? suc n with m ≡ℕ? n
... | yes refl = yes refl
... | no x = no (suc-¬-≡ x)
  where
    suc-¬-≡ : ∀ {m n : ℕ} → ¬ m ≡ n → ¬ (suc m) ≡ (suc n)
    suc-¬-≡ x refl = x refl

-- Reusing ≤ᵇ and proofs of equivalence with ≤ to decide ≤.

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
... | true  | r | s = yes (r tt)
... | false | r | s = no s

-- Erasing Dec down to Bool (or "isYes").

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no x ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

-- If D is Dec A, then T ⌊ D ⌋ is inhabited exactly when A is inhabited.

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt = x

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} a = tt
fromWitness {A} {no x} a = x a

-- Similar ideas when it is the "no" witnesses we want to handle.

isNo : ∀ {A : Set} → Dec A → Bool
isNo (yes _) = false
isNo (no _)  = true

toWitnessFalse : ∀ {A : Set} {D : Dec A} → T (isNo D) → ¬ A
toWitnessFalse {A} {no x} tt = x

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → T (isNo D)
fromWitnessFalse {A} {yes x} ¬a = ¬a x
fromWitnessFalse {A} {no x} ¬a = tt

-- Agda standard library definitions for use of these.

True : ∀ {A : Set} → (D : Dec A) → Set
True Q = T ⌊ Q ⌋ 

False : ∀ {A : Set} → (D : Dec A) → Set
False Q = T (isNo Q)

-- A concrete example.

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

-- Conclusion: use Decidables instead of Booleans!

-- Logical connectives for Decidables.

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ y = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes x₁ = yes ⟨ x , x₁ ⟩ -- split x, y
yes x ×-dec no x₁ = no (λ {⟨ a , b ⟩ → x₁ b})
no x ×-dec y = no (λ {⟨ a , b ⟩ → x a})

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true ∨ y = true
false ∨ y = y

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec y = yes (inj₁ x)
no x ⊎-dec yes x₁ = yes (inj₂ x₁)
no x ⊎-dec no x₁ = no (λ { (inj₁ a) → x a ; (inj₂ b) → x₁ b}) 


not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no λ ¬a → ¬a x
¬? (no x) = yes x

-- A Boolean version of implication.

_⊃_ : Bool → Bool → Bool
true ⊃ true = true
true ⊃ false = false
false ⊃ y = true

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
yes x →-dec yes x₁ = yes λ z → x₁
yes x →-dec no x₁ = no λ f → x₁ (f x)
no x →-dec y = yes λ a → ⊥-elim (x a)

-- 747/PLFA exercise: ErasBoolDec (3 points)
-- Erasure relates boolean and decidable operations.
{--
Case split one variable in a single step since we can make cases shorter by the property of short circuit. 
Then all cases below becomes refl.
--}
∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes x₁) = refl
∧-× (yes x) (no x₁) = refl
∧-× (no x) y = refl

∨-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-× (yes x) y = refl
∨-× (no x) (yes x₁) = refl
∨-× (no x) (no x₁) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no x) = refl

-- 747/PLFA exercise: iff-erasure.

_iff_ : Bool → Bool → Bool
true iff true = true
true iff false = false
false iff true = false
false iff false = true

{--
Case split variables which contain "Dec" seems not feasible in this case, as 
we have no evidence in the fourth case to get the "⊥", which is the goal.
Since we have "_→-dec_" at hand and we know that "_⇔_" is built by two direction of  "_→_".
So we tried a helper function below which get the result "_⇔_" in the pure "Dec" world. 
And we find its all cases can be solved by C-c C-a.
--}
_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
da ⇔-dec db = mk-⇔-in-dec (da →-dec db) (db →-dec da)
  where
  mk-⇔-in-dec : ∀{A B : Set} → Dec (A → B) → Dec(B → A) → Dec(A ⇔ B)
  mk-⇔-in-dec (yes x) (yes x₁) = yes (record { to = x ; from = x₁ })
  mk-⇔-in-dec (yes x) (no x₁) = no (λ z → x₁ (from z))
  mk-⇔-in-dec (no x) (yes x₁) = no (λ z → x (to z))
  mk-⇔-in-dec (no x) (no x₁) = no (λ z → x₁ (from z)) 


{--
Since we have found the good proving of "_⇔-dec_", all four cases becomes refl after case split.
--}
iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋ 
iff-⇔ (yes x) (yes x₁) = refl
iff-⇔ (yes x) (no x₁) = refl
iff-⇔ (no x) (yes x₁) = refl
iff-⇔ (no x) (no x₁) = refl

-- Proof by reflection.
-- Or, getting Agda to construct proofs at compile time.

-- A guarded version of monus.

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m zero _ = m
minus (suc m) (suc n) (s≤s m≤n) = minus m n m≤n

-- But we have to provide proofs.

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

-- Agda will fill in an implicit record type if it can fill in all fields.
-- Since ⊤ is defined as a record type with no fields...
-- We can get Agda to compute a value of type True (n ≤? m).

_-_ : (m n : ℕ) {n≤m : True (n ≤? m)} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

_ : 5 - 3 ≡ 2
_ = refl

-- We will later use this to get Agda to compute parts of proofs
-- that would be annoying for us to provide.

