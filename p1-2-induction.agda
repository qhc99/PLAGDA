import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

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

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- ? C-c C-l | C-c C-c | C-c C-, | C-c C-r
+-assoc′-interactive : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′-interactive zero n p = refl
+-assoc′-interactive (suc m) n p rewrite +-assoc′-interactive m n p = refl

-- Exercise *-distrib-+
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p  = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p = sym (+-assoc p (m * p) (n * p))


-- Exercise *-distrib-+
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl


any-*-0-is-0 : ∀ (n : ℕ) → n * 0 ≡ 0
any-*-0-is-0 zero = refl
any-*-0-is-0 (suc n) = any-*-0-is-0 n

suc-is-+-1 : ∀ (n : ℕ) → suc n ≡ n + 1
suc-is-+-1 zero = refl
suc-is-+-1 (suc n) rewrite suc-is-+-1 n = refl

self-is-self-*-1 : ∀ (n : ℕ) → n ≡ n * 1
self-is-self-*-1 zero = refl
self-is-self-*-1 (suc n) rewrite sym (self-is-self-*-1 n) = refl

n-*-[m+1]≡n+m-*-n : ∀ (m n : ℕ) → n * (m + 1) ≡ n + m * n
n-*-[m+1]≡n+m-*-n m zero = sym (any-*-0-is-0 m)
n-*-[m+1]≡n+m-*-n m (suc n) = {!   !}

--Exercise *-comm
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n = sym (any-*-0-is-0 n)
*-comm (suc m) n  rewrite suc-is-+-1 m = {! !}
-- *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
