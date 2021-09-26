module 747Relations where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym) -- added sym
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- The less-than-or-equal-to relation.

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_

-- Inversion.

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n

inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero

inv-z≤n z≤n = refl

-- Properties.

-- Reflexivity.

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n

≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity.

≤-trans : ∀ {m n p : ℕ} -- note implicit arguments
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p

≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-trans′ : ∀ (m n p : ℕ) -- without implicit arguments
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p

≤-trans′ .0 n p z≤n n≤p = z≤n
≤-trans′ .(suc m) .(suc n) (suc p) (s≤s {m} {n} m≤n) (s≤s n≤p)
 = s≤s (≤-trans′ m n p m≤n n≤p)

-- Antisymmetry.

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m)
  rewrite ≤-antisym m≤n n≤m = refl

-- Total ordering.

-- A definition with parameters.

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

-- An equivalent definition without parameters.

data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n

-- Showing that ≤ is a total order.

≤-total : ∀ (m n : ℕ) → Total m n -- introducing with clause
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward x = forward (s≤s x)
... | flipped x = flipped (s≤s x)


≤-total′ : ∀ (m n : ℕ) → Total m n -- with helper function and where
≤-total′ zero n = forward z≤n
≤-total′ (suc m) zero = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward x) = forward (s≤s x)
    helper (flipped x) = flipped (s≤s x)

-- Splitting on n first gives different code (see PLFA or try it yourself).

-- Monotonicity.

+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m + p ≤ m + q

+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc m) p q p≤q = s≤s (+-monoʳ-≤ m p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p

+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) -- combine above
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q

+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoʳ-≤ m p q p≤q ) (+-monoˡ-≤ m n q m≤n)

-- PLFA exercise: show *-mono-≤.
{--
copy the structrue of +-mono-≤, set holes.
--}
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (*-comm)

*-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m * p ≤ m * q

*-monoʳ-≤ zero p q p≤q = z≤n -- goal: zero ≤ zero, so fill z≤n here
*-monoʳ-≤ (suc m) p q p≤q = +-mono-≤ p q (m * p) (m * q) p≤q (*-monoʳ-≤ m p q p≤q) 
{--
Above goal: p + m * p ≤ q + m * q
The context: p ≤ q and, by induction, (m * q) ≤ (m * q).
We have rule: +-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q, then 
we can get "p + m * p ≤ q + m * q", which is the goal.
--}

{--
Below I just copied the proof of +-monoˡ-≤ and change "+" to "*" everywhere, then prove successed surprisingly!
Do not forget to import "_*_" and "*-comm" accordingly.
--}
*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p

*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

{--
Same as the prove of *-monoˡ-≤, just copy and change "+" to "*".
Since monotonicity of ≤ has its own prove structrue, we can just change a few lines of code to adapt +-mono-≤ to *-mono-≤.
--}
*-mono-≤ : ∀ (m n p q : ℕ) -- combine above
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q

*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoʳ-≤ m p q p≤q ) (*-monoˡ-≤ m n q m≤n)

-- Strict inequality.

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- 747/PLFA exercise: LTTrans (1 point)
-- Prove that < is transitive.
-- Order of arguments changed from PLFA, to match ≤-trans.

{--
Try case split variables and find case split two variable is much more easier to prove than case split only one variable.
First hole has goal: zero < suc n, thus we fill "z<s"
Second hole has goal:　suc m < suc n, which is the ouput is "s<s". Input s<s and refine, we have goal: m < n, and context: 
n<p : n₁ < n, m<n : m < n₁. By induction, we should fill "<-trans m<n n<p".
--}
<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s ((<-trans m<n n<p))

-- 747/PLFA exercise: Trichotomy (2 points)
-- Prove that either m < n, m ≡ n, or m > n for all m and n.

data Trichotomy (m n : ℕ) : Set where
  is-< : m < n → Trichotomy m n
  is-≡ : m ≡ n → Trichotomy m n
  is-> : n < m → Trichotomy m n
{--
Case split both m and n, since we need knowledge both m and n.
First hole has goal: Trichotomy zero zero, so we should apply ≡ rule, input "is-≡" and refine, get goal: zero ≡ zero, which 
is refl, then the answer is "is-≡ refl" here.
Second hole after refine "is-<", we get goal: zero < suc n, which is constructor "z<s", refine input, then answer is "is-< z<s".
Thrid hole after refine "is->", we get goal: zero < suc m, which is same as the above case.
Fourth hole has goal: Trichotomy (suc m) (suc n), it should be proved by induction, which needs a helper function.
--}

m≡n→suc-m≡suc-n : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
m≡n→suc-m≡suc-n refl = refl

{--
For Trichotomy m n, we have three cases.
In the first case, we have m < n in context, by constructor "s<s" we can get suc m < suc n, which is similar to the thrid case.
In the second cases, we need the rule m ≡ n → suc m ≡ suc n, so we set the other helper function above, which is quite easy to prove.
--}
suc-<-trichotomy : ∀ {m n : ℕ} → Trichotomy m n → Trichotomy (suc m) (suc n)
suc-<-trichotomy (is-< x) = is-< (s<s x)
suc-<-trichotomy (is-≡ x) = is-≡ (m≡n→suc-m≡suc-n x)
suc-<-trichotomy (is-> x) = is-> (s<s x)

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = is-≡ refl 
<-trichotomy zero (suc n) = is-< z<s
<-trichotomy (suc m) zero = is-> z<s
<-trichotomy (suc m) (suc n) = suc-<-trichotomy (<-trichotomy m n)

-- PLFA exercise: show +-mono-<.
{--
Since +-mono-< and +-mono-≤ have same prove structrue, we copy the code of +-mono-≤ and change 
"≤" to "<" everywhere. Then solve conflicts rised by compiler, which do not exist in this case.
--}
+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero    p q p<q  =  p<q
+-monoʳ-< (suc n) p q p<q  =  s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n  rewrite +-comm m p | +-comm n p  = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- Prove that suc m ≤ n implies m < n, and conversely,
-- and do the same for (m ≤ n) and (m < suc n).
-- Hint: if you do the proofs in the order below, you can avoid induction
-- for two of the four proofs.


-- 747/PLFA exercise: LEtoLTS (1 point)

≤-<-to : ∀ {m n : ℕ} → m ≤ n → m < suc n
≤-<-to z≤n = z<s --Goal: zero < suc n
≤-<-to (s≤s m≤n) = s<s (≤-<-to m≤n)
-- Goal: suc m < suc (suc n), we can get "m < suc n" from "m ≤ n" and "≤-<-to" by induction, 
-- then by constructor "s<s" we get "suc m < suc (suc n)".

-- 747/PLFA exercise: LEStoLT (1 point)

≤-<--to′ : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-<--to′ (s≤s sm≤n) = ≤-<-to sm≤n --Goal: m < suc n, context: sm≤n : m ≤ n, and we have "≤-<-to : ∀ {m n : ℕ} → m ≤ n → m < suc n"

-- 747/PLFA exercise: LTtoSLE (1 point)
{--
First goal: 1 ≤ suc n. It is actually solved by C-c C-a. 
We have "zero ≤ n" by "z≤n", by "s≤s" it is transformed into suc zero ≤ suc n, which is "1 ≤ suc n".
Second goal: suc (suc m) ≤ suc n, It is again solved by C-c C-a.
By induction we have suc m ≤ n from m < n, then by constructor "s≤s" we get suc (suc m) ≤ suc n 
--}
≤-<-from : ∀ {m n : ℕ} → m < n → suc m ≤ n
≤-<-from z<s = s≤s z≤n 
≤-<-from (s<s m<n)  = s≤s (≤-<-from m<n)

-- 747/PLFA exercise: LTStoLE (1 point)

≤-<-from′ : ∀ {m n : ℕ} → m < suc n → m ≤ n
≤-<-from′ z<s = z≤n
≤-<-from′ (s<s m<sn) = ≤-<-from m<sn

-- PLFA exercise: use the above to give a proof of <-trans that uses ≤-trans.
{--
By "≤-<-from : ∀ {m n : ℕ} → m < n → suc m ≤ n", we have two rules below:
m < n → suc m ≤ n,
n < p → suc n ≤ p.
By ≤-trans we have "suc m ≤ suc n" with a helper function "n ≤ suc n".
Then by ≤-trans again we have "suc m ≤ p" from the fact that "suc m ≤ suc n ≤ p".
Finally, by "≤-<--to′ : ∀ {m n : ℕ} → suc m ≤ n → m < n", we get the goal "m < p"
--}
n≤suc-n : ∀ {n : ℕ} → n ≤ suc n
n≤suc-n {zero} = z≤n
n≤suc-n {suc n} = s≤s n≤suc-n

<-trans-≤-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-≤-trans m<n n<p = ≤-<--to′ (≤-trans (≤-trans (≤-<-from m<n) n≤suc-n) (≤-<-from n<p))
-- Mutually recursive datatypes.
-- Specify the types first, then give the definitions.

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- Theorems about these datatypes.
-- The proofs are also mutually recursive.
-- So we give the types first, then the implementations.

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc x) en = suc (o+e≡o x en)

o+e≡o (suc x) en = suc (e+e≡e x en)

-- 747/PLFA exercise: OPOE (2 points)
-- Prove that the sum of two odds is even.
-- Hint: You will need to define another theorem and prove both
--       by mutual induction, as with the theorems above.         

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)
e+o≡o {m} {n} em on rewrite +-comm m n  = o+e≡o on em

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  --------------
  → even (m + n)

o+o≡e (suc x) (suc x₁) = {!   !}


-- For remarks on which of these definitions are in the standard library, see PLFA.

-- Here is the new Unicode used in this file.

{-

≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

-}