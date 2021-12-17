module Exam where

-- Library

open import Data.Bool using (Bool)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s; _*_)  renaming (_<?_ to _<D_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ)
open import Data.List.Base as List using (List; []; _∷_; length) renaming (map to mapList)
--open import Data.List.Extrema using (max)

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

-- For easier life not using standard library as "_<_" is defined by "_≤_"... 
data _<ℕ_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero <ℕ suc n

  s<s : ∀ {m n : ℕ}
    → m <ℕ n
      -------------
    → suc m <ℕ suc n

-- define _<_ for Int
data _<_ : Int → Int → Set where
    zer<pos : ∀{n : ℕ}
        → zer < pos n

    neg<zer : ∀{n : ℕ}
        → neg n < zer
    
    neg<pos : ∀{n n₁ : ℕ}
        → neg n < pos n₁
    
    pz<pos : ∀{n : ℕ} 
        → zero <ℕ n
        → pos zero < pos n

    suc-pz<pos : ∀{a b : ℕ}
        → pos a < pos b
        → pos (suc a) < pos (suc b)

    neg<nz : ∀{n : ℕ}
        → zero <ℕ n
        → neg n < neg zero   
    
    suc-neg<nz : ∀{a b : ℕ}
        → neg a < neg b
        → neg (suc a) < neg (suc b) 


¬x-<ℕ-x : ∀(x : ℕ) → ¬ (x <ℕ x)
¬x-<ℕ-x zero = λ ()
¬x-<ℕ-x (suc x) = λ { (s<s x<x) → ¬x-<ℕ-x x x<x }

¬pos-x<pos-x : ∀(x : ℕ) → ¬ (pos x < pos x)
¬pos-x<pos-x zero = λ {(pz<pos z<z) → ¬x-<ℕ-x zero z<z}
¬pos-x<pos-x (suc x) = λ {(suc-pz<pos x<x) → ¬pos-x<pos-x x x<x } 

¬neg-x<neg-x : ∀(x : ℕ) → ¬ (neg x < neg x)
¬neg-x<neg-x zero = λ {(neg<nz z<z) → ¬x-<ℕ-x zero z<z}
¬neg-x<neg-x (suc x) = λ {(suc-neg<nz x<x) → ¬neg-x<neg-x x x<x}

suc-both-¬pos-a<pos-b : ∀{a b : ℕ} → ¬ (pos a < pos b) → ¬ (pos (suc a) < pos (suc b))
suc-both-¬pos-a<pos-b {zero} {zero} = λ {x (suc-pz<pos z<z) → x z<z }
suc-both-¬pos-a<pos-b {zero} {suc b} = λ z _ → z (pz<pos z<s)
suc-both-¬pos-a<pos-b {suc a} {zero} = λ {x (suc-pz<pos x<x) → x x<x }
suc-both-¬pos-a<pos-b {suc a} {suc b} = λ {x (suc-pz<pos a<b) → x a<b }

-- symmetric as above
suc-both-¬neg-a<neg-b : ∀{a b : ℕ} → ¬ (neg a < neg b) → ¬ (neg (suc a) < neg (suc b))
suc-both-¬neg-a<neg-b {zero} {zero} = λ {x (suc-neg<nz z<z) → x z<z }
suc-both-¬neg-a<neg-b {zero} {suc b} = λ {x (suc-neg<nz x<x) → x x<x }
suc-both-¬neg-a<neg-b {suc a} {zero} = λ z _ → z (neg<nz z<s)
suc-both-¬neg-a<neg-b {suc a} {suc b} = λ {x (suc-neg<nz a<b) → x a<b }


-- show that this is a decidable property
_<?_ : ∀ (x y : Int) → Dec (x < y)
pos zero <? pos zero = no λ x → ¬pos-x<pos-x zero x
pos zero <? pos (suc x₁) = yes (pz<pos z<s)
pos (suc x) <? pos zero = no (λ ())
pos (suc x) <? pos (suc x₁) with pos x <? pos x₁
... | no ¬p = no (suc-both-¬pos-a<pos-b (λ x₂ → ¬p x₂))
... | yes p = yes (suc-pz<pos p)
pos x <? zer = no (λ ())
pos x <? neg x₁ = no (λ ())
zer <? pos x = yes zer<pos
zer <? zer = no (λ ())
zer <? neg x = no (λ ())
neg x <? pos x₁ = yes neg<pos
neg x <? zer = yes neg<zer
neg zero <? neg zero = no (λ x → ¬neg-x<neg-x zero x)
neg zero <? neg (suc x₁) = no (λ ())
neg (suc x) <? neg zero = yes (neg<nz z<s)
neg (suc x) <? neg (suc x₁)  with neg x <? neg x₁
... | no ¬p = no (suc-both-¬neg-a<neg-b (λ x₂ → ¬p x₂))
... | yes p = yes (suc-neg<nz p)

--

-- The standard library implements Rose Trees (Data.Tree.Rose) but in an odd
-- way using 'sized types' (which we have not covered). Implement them
-- using two constructors instead, where
-- 1) data is at the leaves
-- 2) there is no data in the noces
-- (so that you'll need two constructors).

-- awkward imitation with std library, but it is best I can do before ddl.
data Rose (A : Set)  : ℕ →  Set where
    leaf : A → Rose A 0
    node : ∀ {n} → A → (ts : List (Rose A n)) → Rose A (1 + n)

mapRose : ∀{A B i} → (A → B) → Rose A i → Rose B i
mapRose f (leaf x) = leaf (f x)
mapRose f (node x ts) = node (f x) (mapList (mapRose f) ts)

foldrRose : ∀{A B n} →  (A → (List B) → B) → Rose A n → B
foldrRose f (leaf x) = f x []
foldrRose f (node x ts) = f x (mapList (foldrRose f) ts)

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  Bool.true
⌊ no ¬x ⌋  =  Bool.false

maxℕ : ℕ → ℕ → ℕ
maxℕ a b with ⌊ a <D b ⌋
... | Bool.false = a
... | Bool.true = b

maxListℕ : ℕ → List ℕ → ℕ
maxListℕ a [] = a
maxListℕ a (x ∷ ls) = maxListℕ (maxℕ x a) ls 

depthRose : ∀{A i} → Rose A i → ℕ
depthRose (leaf x) = 0
depthRose (node x ts) = suc (maxListℕ zero (mapList depthRose ts))

-- implement 'map', 'foldr' and 'depth'. Consider leaves to have depth 0.
-- use 'foldr' to get all the data from a Rose tree into a (flat) list

-- build a Rose tree with depth 5 that contains *NO* data at all.

data NULL : Set where

_ : Rose NULL 5
_ = {! node NULL (leaf NULL ∷ [])  !}

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
-- change sucᶜ to return something in the shape of a Church numeral
-- What does twoᶜ · sucᶜ · `unit now reduce to?
{-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
We should have the below rule:

sucᶜ ∙ oneᶜ ≡ twoᶜ
sucᶜ ∙ (ƛ "s" ⇒ ƛ "z" ⇒ (` "s" · ` "z")) ≡  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

Then we have sucᶜ:

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" ·  (` "n" · ` "s" · ` "z")

We have: twoᶜ · sucᶜ · `unit ≡ sucᶜ ∙ sucᶜ ∙ `unit
But to get a meaningful result for "sucᶜ ∙ sucᶜ ∙ `unit", we should set sucᶜ:

sucᶜ : Term
sucᶜ = ƛ "z" ⇒ ƛ "s" ⇒ ` "s" · ` "z"

Then "sucᶜ ∙ sucᶜ ∙ `unit" reduced to "(ƛ "s" ⇒ ` "s" · (ƛ "s" ⇒ ` "s" · ` "z"))"
#####################################################################################
-}

-- ⊢sucᶜ has a different types -- what?
{-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Ch-suc : Type → Type
Ch-suc A  =  A ⇒ (A ⇒ A) ⇒ A
#####################################################################################
-}

-- Modify Properties.agda in the same way, proving progress and preservation.

-- There are 4 Quiz questions at the end of https://plfa.github.io/Properties/.
-- Pick any 2 of them, and answer them.

{-
Quiz
Suppose we add a new term zap with the following reduction rule

-------- β-zap
M —→ zap
and the following typing rule:

----------- ⊢zap
Γ ⊢ zap ⦂ A
Which of the following properties remain true in the presence of these rules? For each property, write either “remains true” or “becomes false.” If a property becomes false, give a counterexample:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Determinism of step : false, any term can either be reduced as usual or be reduced to "zap".

Progress : true, as long as we do not require determinism.

Preservation : true, zap has the same type as original term.
#####################################################################################
-}

{-
Quiz
Suppose instead that we remove the rule ξ·₁ from the step relation. Which of the following properties remain true in the absence of this rule? For each one, write either “remains true” or else “becomes false.” If a property becomes false, give a counterexample:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Determinism of step : true, no ambiguity is introduced.

Progress : false, we cannot reduce a term to a value when the term needs "ξ·₁" to reduce, which is essential.

Preservation : true, the type of a term is intact thought the term cannot be reduced to a value.
#####################################################################################
-}

---------------------------
 