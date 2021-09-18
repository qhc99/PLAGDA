{--
Assignment1 Naturals of Qinghao Chen
--}

module 747Naturals where

-- This is a comment.

{-
  This is a multi-line comment
-}

-- Definition of datatype representing natural numbers. 

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- A couple of definitions using this datatype.

one : ℕ
one = suc zero

two : ℕ
two = suc (suc zero)

-- I could have also said two = suc one.

-- PLFA exercise: write out seven.

-- Pragma to use decimal notation as shorthand.

{-# BUILTIN NATURAL ℕ #-}

-- Some useful imports from the standard library:

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- Addition on naturals.

_+_ : ℕ → ℕ → ℕ
zero + n =  n  
suc m + n =  suc (m + n)  

-- Agda normalization; proof of equality.

_ : 2 + 3 ≡ 5
_ = refl

-- Equational reasoning.

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- many steps condensed
    5
  ∎

-- PLFA shows longhand and shorthand are interchangeable.

-- PLFA exercise: write out the reduction for 3+4 equationally.


-- Multiplication.

_*_ : ℕ → ℕ → ℕ
zero * n =  zero  
suc m * n =  n + m * n  

_ =
  begin
    2 * 3
  ≡⟨⟩    -- many steps condensed
    6
  ∎

-- PLFA exercise: write out 3*4.

-- 747 exercise: Exponentiation (1 point)
-- Define exponentiation (m raised to the power n).
-- 0 ^ 0 = 1 for this exercise.

_^_ : ℕ → ℕ → ℕ
m ^ zero =  suc zero  
m ^ suc n = m * (m ^ n)  

-- One test for exponentiation (you should write others).

_ : 2 ^ 3 ≡ 8
_ = refl

-- Monus (subtraction for naturals, bottoms out at zero).

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
     3 ∸ 2
  ≡⟨⟩ -- many steps condensed
     1
  ∎

_ =
  begin
     2 ∸ 3
  ≡⟨⟩ -- many steps condensed
     0
  ∎

-- PLFA exercise: write out 5 ∸ 3 and 3 ∸ 5.

infixl 6  _+_  _∸_
infixl 7  _*_

-- These pragmas will register our operations, if we want,
-- so that they work with decimal notation.

-- {-# BUILTIN NATPLUS _+_ #-}
-- {-# BUILTIN NATTIMES _*_ #-}
-- {-# BUILTIN NATMINUS _∸_ #-}

-- Binary representation.
-- Modified from PLFA exercise (thanks to David Darais).

data Bin-ℕ : Set where
  bits : Bin-ℕ
  _x0 : Bin-ℕ → Bin-ℕ
  _x1 : Bin-ℕ → Bin-ℕ

-- Our representation of zero is different from PLFA.
-- We use the empty sequence of bits (more consistent).

bin-zero : Bin-ℕ
bin-zero = bits

bin-one : Bin-ℕ
bin-one = bits x1     -- 1 in binary

bin-two : Bin-ℕ
bin-two = bits x1 x0  -- 10 in binary

-- 747 exercise: Increment (1 point)
-- Define increment (add one).

{-- 
Since variable "bits" already denotes zeros of any length, we use variable "other" to represent 
all bits except the rightmost one.
For example, given a sequence "bits x1 x0 x1", variable "other" should be "bits x1 x0" 
--}
inc : Bin-ℕ → Bin-ℕ
inc bits = bits x1 -- increment of bin-zero is bin-one, which is "bits x1" according to context above
inc (other x0) = (other x1) -- when right side is 0, just flip it to 1 and then finish
inc (other x1) = ((inc other) x0) -- when right side is 1, flip it to 0 and then increse other part

-- An example/test of increment (you should create others).

_ : inc (bits x1 x0 x1 x1) ≡ bits x1 x1 x0 x0
_ = refl

-- 747 exercise: To/From (2 points)
-- Define 'tob' and 'fromb' operations
-- to convert between unary (ℕ) and binary (Bin-ℕ) notation.
-- Hint: avoid addition and multiplication,
-- and instead use the provided dbl (double) function.
-- This will make later proofs easier.
-- I've put 'b' on the end of the operations to
-- avoid a name clash in a later file.
-- It also makes the direction clear when using them.

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc m) = suc (suc (dbl m))

tob : ℕ → Bin-ℕ
tob zero =  bits -- in the context above, "bits" is bin-zero, so here should fill "bits" instead of "bits x0" 
tob (suc m) =  inc (tob m) -- successor of decimal number equals increment of equivalent binary number

{--
binary number a b c d equals (d * 2^0 + c * 2^1 + b * 2^2 + a * 2^3) = 2 * a + (2 * b + (2 * c + (d)))
the following two rules evaluate type Bin-ℕ in accordance with the right term above from inner to outer.
--}
fromb : Bin-ℕ → ℕ
fromb bits = zero
fromb (n x0) = dbl (fromb n)  -- 2 * next-term + current-bit = 2 * next-term since x0 is 0
fromb (n x1) = suc (dbl (fromb n)) -- 2 * next-term + current-bit = 2 * next-term + 1 since x1 is 1

-- A couple of examples/tests (you should create others).

_ : tob 6 ≡ bits x1 x1 x0
_ = refl

_ : fromb (bits x1 x1 x0) ≡ 6
_ = refl

-- 747 exercise: BinAdd (2 points)
-- Write the addition function for binary notation.
-- Do NOT use 'to' and 'from'. Work with Bin-ℕ as if ℕ did not exist.
-- Hint: use recursion on both m and n.

{--
It seems that the code below is redundant because one line of code is highlighted by editor, but I cannot simplify it further.
The last 4 cases below is the direct implementation of binary addition.
Evaluation goes from right to left bit by bit. When overflow ocurrs in the current bit, it carries 1 to the next evaluation process.
So call inc on next part of binary sequence.
--}
_bin-+_ : Bin-ℕ → Bin-ℕ → Bin-ℕ
bits bin-+ n = n -- base cases, one of two binary decay to "bits" when they have different length
m bin-+ bits = m
(m x0) bin-+ (n x0) = (m bin-+ n) x0 -- 3 simple cases which dose not carry 1 into former part
(m x0) bin-+ (n x1) = (m bin-+ n) x1
(m x1) bin-+ (n x0) = (m bin-+ n) x1
(m x1) bin-+ (n x1) = (inc (m bin-+ n)) x0 -- final case which carry 1 into former part





-- Tests can use to/from, or write out binary constants as below.
-- Again: write more tests!

_ : (bits x1 x0) bin-+ (bits x1 x1) ≡ (bits x1 x0 x1)
_ = refl
_ : (bits x1 x1) bin-+ (bits x1 x1) ≡ (bits x1 x1 x0)
_ = refl

-- That's it for now, but we will return to binary notation later.

-- Many definitions from above are also in the standard library.

-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

-- Unicode used in this chapter:

{-
    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
-}