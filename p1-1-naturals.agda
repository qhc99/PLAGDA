data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

 -- Exercise 2: +-example (practice)
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩    -- is shorthand for
    (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc ((suc (suc zero)) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩    -- inductive case
    suc (suc ((suc zero) + (suc (suc (suc (suc zero))))))
  ≡⟨⟩    -- inductive case
    suc (suc (suc (zero + (suc (suc (suc (suc zero)))))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩    -- is longhand for
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

-- Exercise 3: *-example (practice)
_ =
  begin
    3 * 4
  ≡⟨⟩    -- inductive case
    4 + (2 * 4)
  ≡⟨⟩    -- inductive case
    4 + (4 + (1 * 4))
  ≡⟨⟩    -- inductive case
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩    -- base case
    4 + (4 + (4 + 0))
  ≡⟨⟩    -- simplify
    12
  ∎

-- Exercise 4: ^-example (practice)
_^_ : ℕ → ℕ → ℕ
n ^ zero = (suc zero)
m ^ (suc n) = m * (m ^ n) 

_ =
  begin
    3 ^ 4
  ≡⟨⟩    -- inductive case
    3 * (3 ^ 3)
  ≡⟨⟩    -- inductive case
    3 * (3 * (3 ^ 2))
  ≡⟨⟩    -- inductive case
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩    -- inductive case
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩    -- base case
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩    -- simplify
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

-- ∸-example₁
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

-- ∸-example₂
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- precedance
infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise Bin
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

BinInc_ : Bin → Bin
BinInc ⟨⟩ = ⟨⟩ I
BinInc (rest O) = (rest I)
BinInc (rest I) = ((BinInc rest) O)

b_zero : Bin
b_zero = ⟨⟩ O

b_one : Bin
b_one = ⟨⟩ I

b_two : Bin
b_two = ⟨⟩ I O

b_three : Bin
b_three = ⟨⟩ I I

b_four : Bin
b_four = ⟨⟩ I O O

b_five : Bin
b_five = ⟨⟩ I O I

_ : BinInc b_zero ≡ b_one; _ = refl
_ : BinInc b_one ≡ b_two; _ = refl
_ : BinInc b_two ≡ b_three; _ = refl
_ : BinInc b_three ≡ b_four; _ = refl
_ : BinInc b_four ≡ b_five; _ = refl

DecToBin   : ℕ → Bin
DecToBin zero = ⟨⟩ O
DecToBin (suc num) = BinInc (DecToBin num)

_ : DecToBin 0 ≡ b_zero; _ = refl
_ : DecToBin 1 ≡ b_one; _ = refl
_ : DecToBin 2 ≡ b_two; _ = refl
_ : DecToBin 3 ≡ b_three; _ = refl
_ : DecToBin 4 ≡ b_four; _ = refl

BinToDec : Bin → ℕ
BinToDec (rest I) = (suc (2 * (BinToDec rest)))
BinToDec (rest O) = 2 * (BinToDec rest)
BinToDec ⟨⟩ = zero

_ : BinToDec b_zero ≡ 0; _ = refl
_ : BinToDec b_one ≡ 1; _ = refl
_ : BinToDec b_two ≡ 2; _ = refl
_ : BinToDec b_three ≡ 3; _ = refl
_ : BinToDec b_four ≡ 4; _ = refl

-- C-c C-d get type of input
-- C-c C-n evaluate