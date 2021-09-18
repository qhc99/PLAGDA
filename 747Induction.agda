module 747Induction where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- PLFA coverage of identity, associativity, commutativity, distributivity.

-- An example of the associative law for addition, presented using equational reasoning.

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- A theorem easy to prove.
-- + is reduction on left term
+-identityᴸ : ∀ (m : ℕ) → zero + m ≡ m
+-identityᴸ m = refl

-- A first nontrivial theorem.
-- An equational proof is shown in PLFA.
-- Instead we will use 'rewrite'.

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

-- PLFA's proof uses helpers cong and sym imported from the standard library,
-- and a form of equational reasoning that allows more elaborate justification than above.
-- We can use cong in place of rewrite.

+-identityʳ′ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ′ zero = refl
+-identityʳ′ (suc m) = cong suc (+-identityʳ′ m)

-- Associativity of addition.
-- (Done first in PLFA.)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p  = refl
--+-assoc (suc m) n p  rewrite +-assoc m n p  =  refl

-- A useful lemma about addition.
-- Equational proof shown in PLFA.

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Commutativity of addition.
-- Equational proof shown in PLFA.

+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

-- 747/PLFA exercise: AddSwap (1 point)
-- Please do this without using induction/recursion.

{--
"(m + n) + p" by [+-comm m n] → "(n + m) + p" by [+-assoc n m p] → "n + (m + p)""
hence "rewrite +-comm m n | +-assoc n m p"
--}
+-swap : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
+-swap m n p rewrite +-comm m n | +-assoc n m p = refl

-- 747/PLFA exercise: AddDistMult (2 points)
-- Show that addition distributes over multiplication.
{--
Solve this exercise by compiler hint of goal.
Case split p has goal on first hole: (m + n) * zero ≡ m * zero + n * zero.
Case split n has goal on first hole: (m + zero) * p ≡ m * p + zero.
Case split m has goal on first hole: n * p ≡ n * p.
So we should split variable m since its goal is refl.
Then second hole has goal: p + (m + n) * p ≡ p + m * p + n * p.
We can see (m + n) * p = m * p + n * p is part of two sides, which is *-+-rdistrib m n p.
Rewrite it, we have goal: p + (m * p + n * p) ≡ p + m * p + n * p, which is symmetric of +-assoc p (m * p) (n * p).
Then we get the answer below
--}
*-+-rdistrib : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-+-rdistrib zero n p = refl 
*-+-rdistrib (suc m) n p rewrite *-+-rdistrib m n p = sym (+-assoc p (m * p) (n * p))

-- 747/PLFA exercise: MultAssoc (2 points)
-- Show that multiplication is associative.
{--
Follow the idea of exercise above, we try split variable m, and first hole is refl, which is a good start.
Second hole has goal: (n + m * n) * p ≡ n * p + m * (n * p).
Obviously, we have (n + m * n) * p ≡ n * p + m * n * p, which is exactly *-+-rdistrib n (m * n) p.
Finally, by induction, we have m * n * p = m * (n * p), then we get the answer.
--}
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-+-rdistrib n (m * n) p | *-assoc m n p = refl

-- 747/PLFA exercise: MultComm (3 points)
-- Show that multiplication is commutative.
-- As with the addition proof above, helper lemmas will be needed.

-- Two rules below are trivial but helpful in the prove
any-*-0-is-0 : ∀ (n : ℕ) → n * zero ≡ zero
any-*-0-is-0 zero = refl
any-*-0-is-0 (suc n) rewrite any-*-0-is-0 n = refl 

suc-is-+-1 : ∀ (n : ℕ) → suc n ≡ n + 1
suc-is-+-1 zero = refl
suc-is-+-1 (suc n) rewrite suc-is-+-1 n = refl

{--
When we use rewrite, two terms in the equation changed at the same time, which is not what we want.
That is, "suc n ≡ suc (n + 1" becomes "suc (n + 1) ≡ suc(n + 1 + 1)".
So in the second case we have to use begin and qed sequence instead of rewrite.
--}
self-is-self-*-1 : ∀ (n : ℕ) → n ≡ n * 1
self-is-self-*-1 zero = refl
self-is-self-*-1 (suc n) = 
  begin
    suc n 
  ≡⟨ cong suc (self-is-self-*-1 n) ⟩
    suc (n * 1) 
  ∎

--In the second case
--Goal at the start:                                        m + n + p * (m + n)       ≡ m + p * m + (n + p * n).
--Goal after rewrite "*-+-ldistrib m n p":                  m + n + (p * m + p * n)   ≡ m + p * m + (n + p * n).
--Goal after rewrite "+-assoc m n (p * m + p * n)":         m + (n + (p * m + p * n)) ≡ m + p * m + (n + p * n).
--Goal after rewrite "sym (+-assoc n (p * m) (p * n))":     m + (n + (p * m + p * n)) ≡ m + p * m + (n + p * n).
--Goal after rewrite "+-comm n (p * m)":                    m + (p * m + n + p * n)   ≡ m + p * m + (n + p * n)
--Goal after rewrite "+-assoc (p * m) n  (p * n)":          m + (p * m + (n + p * n)) ≡ m + p * m + (n + p * n).
--Goal after rewrite "sym (+-assoc m (p * m) (n + p * n))": m + p * m + (n + p * n)   ≡ m + p * m + (n + p * n).
--Then we can see the final goal is itself refl.
*-+-ldistrib : ∀ (m n p : ℕ) → p * (m + n) ≡ p * m + p * n
*-+-ldistrib m n zero = refl
*-+-ldistrib m n (suc p) 
  rewrite *-+-ldistrib m n p | 
  +-assoc m n (p * m + p * n) | 
  sym (+-assoc n (p * m) (p * n)) |
  +-comm n (p * m) | 
  +-assoc (p * m) n  (p * n) | 
  sym (+-assoc m (p * m) (n + p * n)) = refl 

--In the second case
--Goal at the start:                             m * suc n     ≡ m + n * m
--Goal after rewrite "suc-is-+-1 n":             m * (n + 1)   ≡ m + n * m
--Goal after rewrite "*-+-ldistrib n 1 m":       m * n + m * 1 ≡ m + n * m
--Goal after rewrite "*-comm m n":               n * m + m * 1 ≡ m + n * m
--Goal after rewrite "+-comm (n * m) (m * 1)":   m * 1 + n * m ≡ m + n * m
--Goal after rewrite "sym (self-is-self-*-1 m)": m + n * m     ≡ m + n * m
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero = any-*-0-is-0 m
*-comm m (suc n) 
  rewrite suc-is-+-1 n | 
  *-+-ldistrib n 1 m | 
  *-comm m n | 
  +-comm (n * m) (m * 1) | 
  sym (self-is-self-*-1 m) = refl


-- 747/PLFA exercise: LeftMonusZero (1 point)
-- PLFA asks "Did your proof require induction?"
-- (which should give you an indication of the expected answer).

--Since in the proof of second case we have not used the knowledge of "zero ∸ m ≡ zero", the proof does not require induction.
0∸n≡0 : ∀ (m : ℕ) → zero ∸ m ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc m) = refl

-- 747/PLFA exercise: MonusAssocish (2 points)
-- Show a form of associativity for monus.

--Goal of first case: m ∸ n ≡ m ∸ (n + zero)
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m n zero rewrite +-identity n = refl
∸-+-assoc m n (suc p) = {!   !}

-- PLFA exercise (stretch): distributive and associative laws for exponentiation.

-- 747 extended exercise: properties of binary representation.
-- This is based on the PLFA Bin-laws exercise.

-- Copied from 747Naturals.

data Bin-ℕ : Set where
  bits : Bin-ℕ
  _x0 : Bin-ℕ → Bin-ℕ
  _x1 : Bin-ℕ → Bin-ℕ

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

-- Copy your versions of 'inc', 'to', 'from', 'bin-+' over from 747Naturals.
-- You may choose to change them here to make proofs easier.
-- But make sure to test them if you do!

inc : Bin-ℕ → Bin-ℕ
inc bits = bits x1 
inc (other x0) = (other x1) 
inc (other x1) = ((inc other) x0)

tob : ℕ → Bin-ℕ
tob zero =  bits 
tob (suc m) =  inc (tob m) 

fromb : Bin-ℕ → ℕ
fromb bits = zero
fromb (n x0) = dbl (fromb n)  
fromb (n x1) = suc (dbl (fromb n)) 

_bin-+_ : Bin-ℕ → Bin-ℕ → Bin-ℕ
bits bin-+ n = n 
m bin-+ bits = m
(m x0) bin-+ (n x0) = (m bin-+ n) x0
(m x0) bin-+ (n x1) = (m bin-+ n) x1
(m x1) bin-+ (n x0) = (m bin-+ n) x1
(m x1) bin-+ (n x1) = (inc (m bin-+ n)) x0 

-- 747 exercise: DoubleB (1 point)
-- Write the Bin-ℕ version of dbl, here called dblb.
-- As with the other Bin-ℕ operations, don't use tob/fromb.
{--
We know left shift of binary number equals double that number, hence we just have a single rule: dblb m = m x0.
But I found it is not a right answer because of the representation of zero.
dblb bits should always be bits, appending zero to rightmost in this case is wrong.
So we case split variable m, and get three cases.
First cases is special while the other can be simply appended a x0.
--}
dblb : Bin-ℕ → Bin-ℕ
dblb bits = bits
dblb (m x0) = m x0 x0
dblb (m x1) = m x1 x0

-- Here are some properties of tob/fromb/inc suggested by PLFA Induction.
-- Please complete the proofs.

-- 747 exercise: FromInc (1 point)
{--
Since we have only one varaible, case split it find that goals of the first two rules are refl .
Case 3 have the goal: dbl (fromb (inc m)) ≡ suc (suc (dbl (fromb m))).
Since we have known "fromb (inc m) ≡ suc (fromb m)".
"rewrite from∘inc m ", we got goal: suc (suc (dbl (fromb m))) ≡ suc (suc (dbl (fromb m))), 
which is surprisingly refl since it is not obvious before rewrite
--}
from∘inc : ∀ (m : Bin-ℕ) → fromb (inc m) ≡ suc (fromb m)
from∘inc bits = refl
from∘inc (m x0) = refl
from∘inc (m x1) rewrite from∘inc m = refl

-- 747 exercise: FromToB (1 point)
-- goal: fromb (inc (tob m)) ≡ suc m
-- suc (fromb (tob m)) ≡ suc m
{--
Case split variable find its goal is refl
Then second case has goal: fromb (inc (tob m)) ≡ suc m, which is "from∘inc (tob m)" if we see "(tob m)" as a whole
Then its goal become: suc (fromb (tob m)) ≡ suc m
By induction we have known "fromb (tob m) ≡ m", which is "from∘tob m"
Obviously after rewrite we got suc (m) ≡ suc m, which is refl
--}
from∘tob : ∀ (m : ℕ) → fromb (tob m) ≡ m
from∘tob zero = refl
from∘tob (suc m) rewrite from∘inc (tob m) | from∘tob m = refl

-- 747 exercise: ToFromB (2 points)
-- The property ∀ (m : Bin-ℕ) → tob (fromb m) ≡ m cannot be proved.
-- Can you see why?
-- However, this restriction of it can be proved.
{--
I solve this just by trying case split of every variable, then I find when I case split "m≡tn", 
the goal of the hole is "fromb (tob n) ≡ n", which is obviously "from∘tob n".
Case split other variables got wierd goals, which require "tob n" and "fromb m" equal zero.
--}
to/from-corr : ∀ (m : Bin-ℕ) (n : ℕ) → m ≡ tob n → fromb m ≡ n
to/from-corr .(tob n) n refl = from∘tob n

-- Here are a few more properties for you to prove.

-- 747 exercise: DblBInc (1 point)
{--
We just case split the variable and find that goals of all cases are all obvious refl. 
Although all cases are refl, single case "dblb∘inc m = refl" does not compile.
--}
dblb∘inc : ∀ (m : Bin-ℕ) → dblb (inc m) ≡ inc (inc (dblb m)) 
dblb∘inc bits = refl
dblb∘inc (m x0) = refl
dblb∘inc (m x1) = refl



-- 747 exercise: ToDbl (1 point)
{--
Case split, goal hint of first hole is obvious refl.
Goal of second case now is "inc (inc (tob (dbl m))) ≡ dblb (inc (tob m))".
We find that we have "tob (dbl m)" in the left term, which can be transformed by induction.
Rewrite it, we now have goal "inc (inc (dblb (tob m))) ≡ dblb (inc (tob m))".
If we see "tob m" as a whole, then this goal is exactly symmetric of proved rule "dblb∘inc". 
--}
to∘dbl : ∀ (m : ℕ) → tob (dbl m) ≡ dblb (tob m)
to∘dbl zero = refl
to∘dbl (suc m) rewrite to∘dbl m = sym (dblb∘inc (tob m))

-- 747 exercise: FromDblB (1 point)
{--
Case split and then all goals are obviously refl.
Note that single case "from∘dblb m = refl" dose compile even though all cases are refl.
--}
from∘dblb : ∀ (m : Bin-ℕ) → fromb (dblb m) ≡ dbl (fromb m)
from∘dblb bits = refl
from∘dblb (m x0) = refl
from∘dblb (m x1) = refl



-- 747 exercise: BinPlusLInc (2 points)
-- This helper function translates the second case for unary addition
--  suc m + n = suc (m + n)
-- into the binary setting. It's useful in the next proof.
-- Hint: induction on both m and n is needed.

{--
Case split m and n at the same time, we got a long list of code below:
bin-+-linc bits bits = refl
bin-+-linc bits (n x0) = refl
bin-+-linc bits (n x1) = refl
bin-+-linc (m x0) bits = refl
bin-+-linc (m x0) (n x0) = refl
bin-+-linc (m x0) (n x1) = refl
bin-+-linc (m x1) bits = refl
bin-+-linc (m x1) (n x0) = {!  !} --goal: ((inc m bin-+ n) x0) ≡ (inc (m bin-+ n) x0)
bin-+-linc (m x1) (n x1) = {!   !} --goal: ((inc m bin-+ n) x1) ≡ (inc (m bin-+ n) x1)
--}

bin-+-linc : ∀ (m n : Bin-ℕ) → (inc m) bin-+ n ≡ inc (m bin-+ n)
bin-+-linc bits n = {!   !}
bin-+-linc m bits = {!   !}
bin-+-linc (m x0) n = {!   !}
bin-+-linc (m x1) (n x0) = {!  !} 
bin-+-linc (m x1) (n x1) = {!   !}

-- 747 exercise: PlusUnaryBinary (2 points)
-- This theorem relates unary and binary addition.

to∘+ : ∀ (m n : ℕ) → tob (m + n) ≡ tob m bin-+ tob n
to∘+ m n = {!!}

-- This ends the extended exercise.


-- The following theorems proved in PLFA can be found in the standard library.

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

-- Unicode used in this chapter:

{-

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

-}