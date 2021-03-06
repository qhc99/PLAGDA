module 747Lists where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import 747Connectives using (_⊎_)

-- Copied from 747Isomorphism.

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


-- Polymorphic lists (parameterized version).

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

-- An example.

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

-- An equivalent indexed version

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

-- Putting the implicit arguments into our example (but why?).

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

-- This pragma would tell Agda to use Haskell lists internally.
-- {-# BUILTIN LIST List #-}

-- Some useful syntax to let us write short lists quickly.

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

-- Append for lists.

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 , 2 , 4 ] ++ [ 3 , 5 ] ≡ [ 0 , 2 , 4 , 3 , 5 ]
_ = refl

-- Associativity of append.
-- Equational reasoning proof in PLFA.

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

-- Left and right identity for append.

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl

-- Length of a list.

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ = refl

-- Reasoning about length.

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys rewrite length-++ xs ys = refl

-- Reverse using structural recursion (inefficient).

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ = refl

-- 747/PLFA exercise: RevCommApp (1 point)
-- How reverse commutes with ++.
-- Changed from PLFA to make xs and ys explicit arguments.

∷→++ : ∀ {A : Set} (x : A) (xs : List A) → x ∷ xs ≡ [ x ] ++ xs
∷→++ x xs = refl 

{--
This exercise can be done by induction on only one variable.
Case split on two variables makes thing a bit more complex.
Two cases are easy to prove, no more comments there. 
--}
reverse-++-commute : ∀ {A : Set} (xs ys : List A)
 → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute [] ys = sym (++-identityʳ (reverse ys))
reverse-++-commute (x ∷ xs) ys rewrite reverse-++-commute xs ys = ++-assoc (reverse ys) (reverse xs) [ x ]

-- 747/PLFA exercise: RevInvol (1 point)
-- Reverse is its own inverse.
-- Changed from PLFA to make xs explicit.
{--
Case split the only variable.
Two cases are easy to prove, no more comments there. 
--}
reverse-involutive : ∀ {A : Set} (xs : List A)
 → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-commute (reverse xs) [ x ] | reverse-involutive xs = refl

-- Towards more efficient reverse (linear time vs quadratic)
-- Shunt is a generalization of reverse.

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

-- A good explanation of what shunt is doing.

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
-- need to rearrange parens on RHS of goal equation
-- now we can apply recursion
shunt-reverse (x ∷ xs) ys
  rewrite ++-assoc (reverse xs) [ x ] ys | shunt-reverse xs (x ∷ ys)
    = refl

-- Now it's clear that more efficient reverse is a special case of shunt.

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

-- Confirmation that the two functions are equivalent.

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs rewrite shunt-reverse xs []
  = ++-identityʳ (reverse xs)

-- Some common higher-order list functions.

-- 'map' applies a function to every element of a list.

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = refl

-- An example of using map.

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = refl

-- 747/PLFA exercise: MapCompose (1 point)
-- The map of a composition is the composition of maps.
-- Changed from PLFA: some arguments made explicit, uses pointwise equality.
{--
Only "xs" can be case split by it inherent structure.
Two cases are easy to prove, no more comments there. 
--}
map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
 → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) rewrite map-compose f g xs = refl

-- 747/PLFA exercise: MapAppendDist (1 point)
-- The map of an append is the append of maps.
-- Changed from PLFA: some arguments made explicit.
{--
This exercise can be done by induction on only one variable.
Case split two lists make things a bit more complex.
Two cases are easy to prove, no more comments there. 
--}
map-++-dist : ∀ {A B : Set} (f : A → B) (xs ys : List A)
 →  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-dist f [] ys = refl
map-++-dist f (x ∷ xs) ys rewrite map-++-dist f xs ys = refl

-- PLFA exercise: map over trees
-- Here is a definition of trees with
-- leaves labelled with type A and internal nodes with type B.

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

-- Write map for Trees.
{--
When reach the leaf, just convert.
When reach the node, convert the node and recursivly convert its left and right tree.
--}
map-Tree : ∀ {A B C D : Set}
  → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node t x t₁) = node (map-Tree f g t) (g x) (map-Tree f g t₁)

-- Fold-right: put operator ⊗ between each list element (and supplied final element).
--             ⊗ is considered right-associative.
-- Fold-right is universal for structural recursion on one argument.

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl

-- Summing a list using foldr.

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl

-- PLFA exercise: use foldr to define product on lists of naturals

List-Π : ∀ (xs : List ℕ) → ℕ
List-Π xs = foldr _*_ 1 xs

_ : (List-Π [ 1 , 2 , 3 , 4 ]) ≡ 24
_ = refl

_ : (List-Π [ 2021 ]) ≡ 2021
_ = refl

-- 747/PLFA exercise: FoldrOverAppend (1 point)
-- Show that foldr over an append can be expressed as
-- foldrs over each list.
{--
This exercise can be done by induction on only one variable.
Case split two lists make things a bit more complex.
Two cases are easy to prove, no more comments there. 
--}
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e  xs ys = refl

-- 747/PLFA exercise: MapIsFoldr (1 point)
-- Show that map can be expressed as a fold.
-- Changed from PLFA: some arguments made explicit, uses pointwise equality.
{--
Case split the only list.
Two cases are easy to prove, no more comments there. 
--}
map-is-foldr : ∀ {A B : Set} (f : A → B) (xs : List A) →
  map f xs ≡ foldr (λ x rs → f x ∷ rs) [] xs
map-is-foldr f [] = refl
map-is-foldr f (x ∷ xs) rewrite map-is-foldr f xs = refl

-- PLFA exercise: write a fold for trees
{-
Recursive in the second case and end in the first case. Then reduce back to the root of the tree.
-}
fold-Tree : ∀ {A B C : Set}
   → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node t x t₁) = g (fold-Tree f g t) x (fold-Tree f g t₁)

-- PLFA exercise: the downFrom function computes a countdown list
-- Prove an equality about its sum


downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

sum-∷ : ∀ (x : ℕ) → (xs : List ℕ) → sum (x ∷ xs) ≡ x + sum xs
sum-∷ x [] = refl
sum-∷ x (x₁ ∷ xs) = refl

open import 747Induction using (*-+-rdistrib; *-comm; +-comm)

n*suc-n≡n*n+n : ∀ (n : ℕ) → n * suc n ≡ n * n + n
n*suc-n≡n*n+n n rewrite *-comm n (suc n) | +-comm n (n * n)  = refl

monus-self : ∀ (n : ℕ) → n ∸ n ≡ 0
monus-self zero = refl
monus-self (suc n) = monus-self n

n*[n∸1]≡n*n∸n : ∀ (n : ℕ) → n * (n ∸ 1) ≡ n * n ∸ n
n*[n∸1]≡n*n∸n zero = refl
n*[n∸1]≡n*n∸n (suc n) 
  rewrite 
  n*suc-n≡n*n+n n | 
  sym (+-assoc n (n * n) n) = {!   !}

sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) 
  rewrite 
  sum-∷ n (downFrom n) | 
  *-+-rdistrib n (sum (downFrom n)) 2 |
  sum-downFrom n | n*[n∸1]≡n*n∸n n = {!   !}




-- 'Monoid' is a mathematical term for a set with an associative operator
-- and an element which is the left and right identity (eg lists).

record IsMonoid (A : Set) : Set where
  field
    id : A
    _⊗_ : A → A → A
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → id ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ id ≡ x

-- The following open command is different from PLFA; it uses instance arguments,
-- which work like typeclasses in Haskell (allow overloading, which is cleaner).

open IsMonoid {{ ...}} public

-- These pragmas make displays of goal and context look nicer.

{-# DISPLAY IsMonoid.id _ = id #-}
{-# DISPLAY IsMonoid._⊗_ _ = _⊗_ #-}

-- We can now describe instances of Monoid using the following notation.

instance

 +-monoid : IsMonoid ℕ
 IsMonoid.id +-monoid = 0
 IsMonoid._⊗_ +-monoid = _+_
 IsMonoid.assoc +-monoid = +-assoc
 IsMonoid.identityˡ +-monoid = +-identityˡ
 IsMonoid.identityʳ +-monoid = +-identityʳ

 *-monoid : IsMonoid ℕ
 IsMonoid.id *-monoid = 1
 IsMonoid._⊗_ *-monoid = _*_
 IsMonoid.assoc *-monoid = *-assoc
 IsMonoid.identityˡ *-monoid = *-identityˡ
 IsMonoid.identityʳ *-monoid = *-identityʳ

 ++-monoid : ∀ {A : Set} → IsMonoid (List A)
 IsMonoid.id ++-monoid = []
 IsMonoid._⊗_ ++-monoid = _++_
 IsMonoid.assoc ++-monoid = ++-assoc
 IsMonoid.identityˡ ++-monoid = ++-identityˡ
 IsMonoid.identityʳ ++-monoid = ++-identityʳ

-- A property of foldr over a monoid.

foldr-monoid : ∀ {A : Set} → {{m : IsMonoid A}} →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ (foldr _⊗_ id xs) ⊗ y
foldr-monoid [] y = sym (identityˡ y)
foldr-monoid (x ∷ xs) y rewrite foldr-monoid xs y = sym (assoc x (foldr _⊗_ id xs) y)

-- How foldr commutes with ++ over a monoid.

foldr-monoid-++ : ∀ {A : Set} → {{m : IsMonoid A}} →
  ∀ (xs ys : List A) → foldr _⊗_ id (xs ++ ys) ≡ foldr _⊗_ id xs ⊗ foldr _⊗_ id ys
foldr-monoid-++ xs ys rewrite foldr-++ _⊗_ id xs ys = foldr-monoid xs (foldr _⊗_ id ys)

-- 747/PLFA exercise: Foldl (1 point)
-- Define foldl, which associates left instead of right, e.g.
--   foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
--   foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z
{-
result is saved in the second argument and reduced to the result at the end of list.
-}
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

-- 747/PLFA exercise: FoldrMonFoldl (2 points)
-- Show that foldr and foldl compute the same value on a monoid
-- when the base case is the identity.
-- Hint: write a helper function for when the base case of foldl is an arbitrary value.

{-
The first case is easy to prove.
For the second case, we have sequence of rewrite below.
Goal at the start:                                "foldl _⊗_ (y ⊗ x) xs ≡ (y ⊗ foldl _⊗_ (id ⊗ x) xs)"
After rewrite "foldl-monoid xs (y ⊗ x)": "((y ⊗ x) ⊗ foldl _⊗_ id xs) ≡ (y ⊗ foldl _⊗_ x xs)"
After rewrite "identityˡ x":              "((y ⊗ x) ⊗ foldl _⊗_ id xs) ≡ (y ⊗ foldl _⊗_ (id ⊗ x) xs)"
After rewrite "foldl-monoid xs x":        "((y ⊗ x) ⊗ foldl _⊗_ id xs) ≡ (y ⊗ (x ⊗ foldl _⊗_ id xs))"
Then the goal becomes "assoc y x (foldl _⊗_ id xs)".
-}
foldl-monoid : ∀ {A : Set} → {{m : IsMonoid A}} →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ (foldl _⊗_ id xs)
foldl-monoid [] y = sym (identityʳ y)
foldl-monoid {A} {{m}} (x ∷ xs) y 
  rewrite 
  foldl-monoid xs (y ⊗ x) | 
  identityˡ x | 
  foldl-monoid xs x 
  = assoc y x (foldl _⊗_ id xs)

{--
Case split on "List" type variable.
The first case is easy to prove.
For the second case, we show transformation below:
Goal at the start:                    "foldl _⊗_ (id ⊗ x) xs ≡ (x ⊗ foldr _⊗_ id xs)"
After rewrite "sym (foldl-r-mon xs)": "foldl _⊗_ (id ⊗ x) xs ≡ (x ⊗ foldl _⊗_ id xs)"
After rewrite "identityˡ x":                  "foldl _⊗_ x xs ≡ (x ⊗ foldl _⊗_ id xs)".
Then the goal becomes "foldl-monoid xs x"
--}
foldl-r-mon : ∀ {A : Set} → {{m : IsMonoid A}} →
  ∀ (xs : List A) → foldl _⊗_ id xs ≡ foldr _⊗_ id xs
foldl-r-mon [] = refl
foldl-r-mon (x ∷ xs) rewrite sym (foldl-r-mon xs) | identityˡ x  = foldl-monoid xs x


-- Inductively-defined predicates over lists

-- All P xs means P x holds for every element of xs

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- Any P xs means P x holds for some element of xs

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
infix 4 _∈_ _∉_

-- membership in list as application of Any

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

-- The development in PLFA, repeated with our notation.

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
to (All-++-⇔ [] ys) apxs++ys = ⟨ [] , apxs++ys ⟩
to (All-++-⇔ (x ∷ xs) ys) (px ∷ apxs++ys)
 with _⇔_.to (All-++-⇔ xs ys) apxs++ys
... | ⟨ apxs , apys ⟩ = ⟨ (px ∷ apxs) , apys ⟩
from (All-++-⇔ [] ys) ⟨ apxs , apys ⟩ = apys
from (All-++-⇔ (x ∷ xs) ys) ⟨ px ∷ apxs , apys ⟩
  = px ∷ _⇔_.from (All-++-⇔ xs ys) ⟨ apxs , apys ⟩


-- PLFA exercise: state and prove Any-++-⇔, and use it to demonstrate
-- an equivalence relating ∈ and _++_.
{-
Spend way too much time than expected!
So I will not try other bonus parts and they were commented away.
-}
{-
Must case split all three variables, then all cases are easy to prove.
-}
any-extend : ∀ {A : Set} {P : A → Set} (xs ys : List A) →  Any P xs →  Any P (xs ++ ys)
any-extend [] [] ()
any-extend [] (x ∷ ys) ()
any-extend (x ∷ xs) [] (here x₁) = here x₁
any-extend (x ∷ xs) [] (there a) rewrite ++-identityʳ (x ∷ xs) = there a
any-extend (x ∷ xs) (x₁ ∷ ys) (here x₂) = here x₂
any-extend (x ∷ xs) (x₁ ∷ ys) (there a) = there (any-extend xs (x₁ ∷ ys) a)

{-
It seems that we need some small but trickey helper functions there.
-}
any-preextend : ∀ {A : Set} {P : A → Set} (xs ys : List A) →  Any P ys →  Any P (xs ++ ys)
any-preextend [] .(_ ∷ _) (here x) = here x
any-preextend [] .(_ ∷ _) (there a) = there a
any-preextend (x ∷ xs) .(_ ∷ _) (here x₁) = {!   !}
any-preextend (x ∷ xs) .(_ ∷ _) (there a) = {!   !}


Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ {A} {P}  xs ys = record { to = Any-++-⇔-to ; from = Any-++-⇔-from }
  where
  Any-++-⇔-to : Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  Any-++-⇔-to x = {!  !}

  Any-++-⇔-from : Any P xs ⊎ Any P ys → Any P (xs ++ ys)
  Any-++-⇔-from (_⊎_.inj₁ x) = any-extend xs ys x
  Any-++-⇔-from (_⊎_.inj₂ x) = {!   !}


-- PLFA exercise: Show that the equivalence All-++-⇔ can be extended to an isomorphism.

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys = {!   !}

-- PLFA exercise: Here is a universe-polymorphic version of composition,
-- and a version of DeMorgan's law for Any and All expressed using it.

_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)


¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
¬Any≃All¬ P xs = {!!}


-- Can we prove the following? If not, explain why.

¬All≃Any¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘′ All P) xs ≃ Any (¬_ ∘′ P) xs
¬All≃Any¬ = {!   !}

-- End of PLFA exercise

-- Decidability of All

-- A Boolean analogue of All

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

-- A Dec analogue of All

-- A definition of a predicate being decidable

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? [] = yes [] 
All? P? (x ∷ xs) with P? x | All? P? xs
All? P? (x ∷ xs) | yes p | yes p₁ = yes (p ∷ p₁)
All? P? (x ∷ xs) | yes p | no ¬p = no (λ { (x ∷ x₁) → ¬p x₁})
All? P? (x ∷ xs) | no ¬p | _ = no (λ { (x ∷ x₁) → ¬p x})

-- PLFA exercise: repeat above for Any


Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? dp = {!   !}


-- PLFA exercises: All-∀ and Any-∃
-- You will need the stronger version of extensionality
-- (for dependent function types) given in PLFA Isomorphism.


All-∀-iso = ∀ {A : Set} {x : A} {P : A → Set} {xs : List A} → x ∈ xs → P x
Any-∃-iso = ∀ {A : Set} {x : A} {P : A → Set} {xs : List A} → ∃[ x ] (x ∈ xs × P x)

All-∀-≃ : ∀ {A : Set} {x : A} {P : A → Set} {xs : List A} →  All P xs ≃ (x ∈ xs → P x)
All-∀-≃ = {!   !}

Any-∃-≃ : ∀ {A : Set} {x : A} {P : A → Set} {xs : List A} → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃-≃ = {!   !}


-- PLFA exercise: a version of 'filter' for decidable predicates


filter? : ∀ {A : Set} {P : A → Set}
  → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
filter? P? xs = {!   !}
