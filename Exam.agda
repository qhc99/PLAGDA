module Exam where

-- Library

open import Data.Bool using (Bool)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_) renaming ( _≤?_ to _≤D_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ)
--open import plfa.part1.Decidable using (_≤?_;_<?_)

open import Isomorphism 
open _≃_

-- You may use anything from the standard library that you find useful

-- Prove that 2 + 2 ≃ 2 × 2
twos : Bool ⊎ Bool ≃ Bool × Bool
twos = mk-≃ twos-to twos-from twos-to-from twos-from-to
    where
    twos-to : Bool ⊎ Bool → Bool × Bool
    twos-to (inj₁ Bool.false) = Bool.false , Bool.false -- 1, match the first line of "twos-form"  
    twos-to (inj₁ Bool.true) = Bool.true , Bool.true    -- 4
    twos-to (inj₂ Bool.false) = Bool.true , Bool.false  -- 3
    twos-to (inj₂ Bool.true) = Bool.false , Bool.true   -- 2

    twos-from : Bool × Bool → Bool ⊎ Bool
    twos-from (Bool.false , Bool.false) = inj₁ Bool.false
    twos-from (Bool.false , Bool.true) = inj₂ Bool.true
    twos-from (Bool.true , Bool.false) = inj₂ Bool.false
    twos-from (Bool.true , Bool.true) = inj₁ Bool.true

    -- to prove the two rules below, we need to care about the matching relation above
    twos-to-from : (x : Bool ⊎ Bool) → twos-from (twos-to x) ≡ x
    twos-to-from (inj₁ Bool.false) = refl
    twos-to-from (inj₁ Bool.true) = refl
    twos-to-from (inj₂ Bool.false) = refl
    twos-to-from (inj₂ Bool.true) = refl

    twos-from-to : (y : Bool × Bool) → twos-to (twos-from y) ≡ y
    twos-from-to (Bool.false , Bool.false) = refl
    twos-from-to (Bool.false , Bool.true) = refl
    twos-from-to (Bool.true , Bool.false) = refl
    twos-from-to (Bool.true , Bool.true) = refl

-- Show that the proof above is NOT 'canonical' by
-- giving another proof but such that the two proofs
-- don't compose to give the identity
twos′ : Bool ⊎ Bool ≃ Bool × Bool
twos′ = mk-≃ twos'-to twos'-from twos'-to-from twos'-from-to
    where
    twos'-to : Bool ⊎ Bool → Bool × Bool
    twos'-to (inj₁ Bool.false) = Bool.true , Bool.true 
    twos'-to (inj₁ Bool.true) = Bool.false , Bool.false   
    twos'-to (inj₂ Bool.false) = Bool.false , Bool.true 
    twos'-to (inj₂ Bool.true) = Bool.true , Bool.false    

    twos'-from : Bool × Bool → Bool ⊎ Bool
    twos'-from (Bool.false , Bool.false) = inj₁ Bool.true -- 2
    twos'-from (Bool.false , Bool.true) = inj₂ Bool.false -- 3 
    twos'-from (Bool.true , Bool.false) = inj₂ Bool.true  -- 4
    twos'-from (Bool.true , Bool.true) = inj₁ Bool.false  -- 1

    twos'-to-from : (x : Bool ⊎ Bool) → twos'-from (twos'-to x) ≡ x
    twos'-to-from (inj₁ Bool.false) = refl
    twos'-to-from (inj₁ Bool.true) = refl
    twos'-to-from (inj₂ Bool.false) = refl
    twos'-to-from (inj₂ Bool.true) = refl

    twos'-from-to : (y : Bool × Bool) → twos'-to (twos'-from y) ≡ y
    twos'-from-to (Bool.false , Bool.false) = refl
    twos'-from-to (Bool.false , Bool.true) = refl
    twos'-from-to (Bool.true , Bool.false) = refl
    twos'-from-to (Bool.true , Bool.true) = refl

-- to prove this, we need to craft cases above for contradiction
twos∘twos′≄id : Σ (Bool ⊎ Bool) (λ x → ¬ (from twos′ (to twos x) ≡ x))
Data.Product.proj₁ twos∘twos′≄id = inj₁ Bool.false
Data.Product.proj₂ twos∘twos′≄id ()

--

-- Here is the "induction principle" for ℕ
indℕ : (P : ℕ → Set) → P 0 → ({n : ℕ} → P n → P (suc n)) → (∀ m → P m)
indℕ P P0 Psuc zero = P0
indℕ P P0 Psuc (suc m) = Psuc (indℕ P P0 Psuc m)

-- Use indℕ to define plus. Hint: indℕ is equivalent to pattern-matching on an element of ℕ.

record Wrap (n : ℕ) :  Set where
    constructor mk-Wrap
    field
        natural : ℕ 

Wrap-suc : ∀{t : ℕ} →  Wrap t → Wrap (suc t)
Wrap-suc (mk-Wrap natural) = mk-Wrap (suc natural)

-- since suc is not type "ℕ → Set", we create a "Wrap" to pass around the limitation
-- induction add suc on "m" but at base we set it as "n"
plus : ℕ → ℕ → ℕ
plus m n = Wrap.natural (indℕ Wrap (mk-Wrap n) (Wrap-suc) m) 

-- prove that it is indeed equal to _+_
plus-correct : ∀ m {n} → plus m n ≡ m + n
plus-correct zero = refl
plus-correct (suc m) {n} rewrite plus-correct m {n = n} = refl

--

-- Consider the following alternate definitions of the integers
data Int : Set where
  pos : ℕ → Int
  zer :     Int
  neg : ℕ → Int

-- Prove that this is equivalent to ℤ
Int≃ℤ : Int ≃ ℤ
Int≃ℤ = mk-≃ Int≃ℤ-to Int≃ℤ-from Int≃ℤ-to-from Int≃ℤ-from-to
    where
    Int≃ℤ-to : Int → ℤ
    Int≃ℤ-to (pos x) = ℤ.pos (suc x)
    Int≃ℤ-to zer = ℤ.pos zero
    Int≃ℤ-to (neg x) = ℤ.negsuc x

    Int≃ℤ-from : ℤ → Int
    Int≃ℤ-from (ℤ.pos zero) = zer
    Int≃ℤ-from (ℤ.pos (suc n)) = pos n
    Int≃ℤ-from (ℤ.negsuc n) = neg n

    Int≃ℤ-to-from : (x : Int) → Int≃ℤ-from (Int≃ℤ-to x) ≡ x
    Int≃ℤ-to-from (pos x) = refl
    Int≃ℤ-to-from zer = refl
    Int≃ℤ-to-from (neg x) = refl

    Int≃ℤ-from-to : (y : ℤ) → Int≃ℤ-to (Int≃ℤ-from y) ≡ y
    Int≃ℤ-from-to (ℤ.pos zero) = refl
    Int≃ℤ-from-to (ℤ.pos (suc n)) = refl
    Int≃ℤ-from-to (ℤ.negsuc n) = refl


-- implement plus for Int
_+Int_ : Int → Int → Int
pos x +Int pos x₁ = pos (x + x₁ + 1)
pos x +Int zer = pos x
pos zero +Int neg zero = zer
pos zero +Int neg (suc x₁) = neg x₁
pos (suc x) +Int neg zero = pos x
pos (suc x) +Int neg (suc x₁) = pos x +Int neg x₁
zer +Int pos x = pos x
zer +Int zer = zer
zer +Int neg x = neg x
neg zero +Int pos zero = zer
neg zero +Int pos (suc x₁) = pos x₁
neg (suc x) +Int pos zero = neg x
neg (suc x) +Int pos (suc x₁) = neg x +Int pos x₁
neg x +Int zer = neg x
neg x +Int neg x₁ = neg (x + x₁ + 1)


-- show that it is equivalent
+-equiv : (x y : Int) → x +Int y ≡ from Int≃ℤ (to Int≃ℤ x +ℤ to Int≃ℤ y)
+-equiv (pos x) (pos x₁) rewrite +-comm 1 x₁ | sym (+-assoc x x₁ 1) = refl
+-equiv (pos x) zer rewrite +-identityʳ x = refl
+-equiv (pos zero) (neg zero) = refl
+-equiv (pos zero) (neg (suc x₁)) = refl
+-equiv (pos (suc x)) (neg zero) = refl
+-equiv (pos (suc x)) (neg (suc x₁)) = +-equiv (pos x) (neg x₁)
+-equiv zer (pos x) = refl
+-equiv zer zer = refl
+-equiv zer (neg x) = refl
+-equiv (neg zero) (pos zero) = refl
+-equiv (neg zero) (pos (suc x₁)) = refl
+-equiv (neg (suc x)) (pos zero) = refl
+-equiv (neg (suc x)) (pos (suc x₁)) = +-equiv (neg x) (pos x₁)
+-equiv (neg zero) zer = refl
+-equiv (neg (suc x)) zer = refl
+-equiv (neg zero) (neg zero) = refl
+-equiv (neg zero) (neg (suc x₁)) rewrite +-comm x₁ 1 = refl
+-equiv (neg (suc x)) (neg zero) rewrite +-identityʳ x | +-comm x 1 = refl
+-equiv (neg (suc x)) (neg (suc x₁)) rewrite +-comm (suc x₁) 1 | +-comm (x + suc x₁) 1 = refl


-- define _<_ for Int
_<_ : Int → Int → Set
a < b = {!   !}

-- show that this is a decidable property
_<?_ : ∀ (x y : Int) → Dec (x < y)
x <? y = {!!}

--

-- The standard library implements Rose Trees (Data.Tree.Rose) but in an odd
-- way using 'sized types' (which we have not covered). Implement them
-- using two constructors instead, where
-- 1) data is at the leaves
-- 2) there is no data in the noces
-- (so that you'll need two constructors).

-- data Rose (A : Set) : Set where

-- implement 'map', 'foldr' and 'depth'. Consider leaves to have depth 0.
-- use 'foldr' to get all the data from a Rose tree into a (flat) list

-- build a Rose tree with depth 5 that contains *NO* data at all.

-- Bonus: build a variant of the above
-- data Rose′ (A : Set) : ℕ → ℕ → Set where
-- where the first natural number counts the number of data in the tree,
-- and the second is the branching factor
-- and Vec is used instead of List. Furthermore, arrange your constructors
-- so as to make it impossible to build an example like the above (depth 5 with no data).
-- Implement 'map', 'foldr' and 'depth'.
-- What interesting theorems can you prove about Rose′ ?

----------------------------

-- Take Lambda.agda (the one that is 'filled' from the course materials)
-- remove `zero, `suc and case_[zero⇒_|suc_⇒_] from values and `ℕ from the types;
--  add `unit to the values and `⊤ to the types.
--   (remove everything that is directly about those 3 items, except for the Church-numerals)
-- change sucᶜ to return something in the shapre of a Church numeral
-- What does twoᶜ · sucᶜ · `unit now reduce to?
-- ⊢sucᶜ has a different types -- what?

-- Modify Properties.agda in the same way, proving progress and preservation.

-- There are 4 Quiz questions at the end of https://plfa.github.io/Properties/.
-- Pick any 2 of them, and answer them.

---------------------------
