module 747More where

-- Libraries.

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app ;cong₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

-- Syntax. (Several of these are new.)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _`×_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
{-
write rules of Boolean by ourselves.

Syntax:
  A, B, C ::= ...                     Types
    Bool                              boolean

  L, M, N ::= ...                     Terms
    L && M                            and
    L || M                            or
    ! L                               not 
    caseB L M N                       caseB

  V, W ::= ...                        Values
    `true                             true
    `false                            false


Typing:  
  --------------- `true
  Γ ⊢ `true : Bool    

  --------------- `false
  Γ ⊢ `false : Bool

  Γ ⊢ V : Bool
  Γ ⊢ W : Bool  
  --------------- _`&&_
  Γ ⊢ V `&& W : Bool
  
  Γ ⊢ V : Bool
  Γ ⊢ W : Bool  
  ---------------- _`||_
  Γ ⊢ V `|| W : Bool

  Γ ⊢ V  : Bool
  ---------------- `!_
  Γ ⊢ `! V : Bool

  Γ ⊢ L : Bool
  Γ ⊢ M ⦂ A
  Γ ⊢ N ⦂ A
  ---------------- caseB
  Γ ⊢ caseB L [`true ⇒ M |`false  ⇒ N ] ⦂ A

Reduction

  L —→ L′
  ----------------- ξ-and₁
  L `&& M —→ L′ `&&  M

  M —→ M′
  ----------------- ξ-and₂
  V `&& M —→ V `&& M′

  ----------------- β-and-true₁
  `true `&& `true —→ `true

  ----------------- β-and-false₁
  `true `&& `false —→ `false

  ----------------- β-and-false₂
  `false `&& `true —→ `false

  ----------------- β-and-false₃
  `false `&& `false —→ `false

  L —→ L′
  ----------------- ξ-or₁
  L `|| M —→ L′ `||  M

  M —→ M′
  ----------------- ξ-or₂
  V `|| M —→ V `|| M′

  ----------------- β-or-true₁
  `true `|| `true —→ `true

  ----------------- β-or-true₂
  `true `|| `false —→ `true

  ----------------- β-or-true₃
  `false `|| `true —→ `true

  ----------------- β-or-false₁
  `false `|| `false —→ `false

  L —→ L′
  ----------------- ξ-not
  `! L  —→ `! L

  ----------------- β-not-true
  `! false —→ `true

  ----------------- β-not-false
  `! `true —→ `false

  L —→ L′
  ----------------------------------------ξ-caseB
  caseB L M N —→ caseB L′ M N

  -----------------------------β-caseB-true
  → caseB `true M N  —→  M

  -----------------------------β-caseB-false
  → caseB `false M N  —→ N
-}
-- Types (third and fourth are new).

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Nat   : Type
  _`×_  : Type → Type → Type
  `⊥   : Type
  _`⊎_  : Type → Type → Type
  `⊤    : Type
  `List_ : Type → Type
  `Bool : Type

-- Contexts (unchanged).

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

-- Variables / lookup judgments (unchanged)

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B
-- Typing
-- Types / type judgments
-- (additions for primitive numbers and products)

data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----
    → Γ ⊢ A

  -- fixpoint

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A

  -- primitive numbers

  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ B

  -- products

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ B

  -- alternative formulation of products

  case× : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      --------------
    → Γ ⊢ C
  
  {-
  We see how the typing rule of "Alternative formulation of products" is transformed into 
  "case×" above and we get "case⊥" by analogy.
  It means we can get any type if we have type "Empty".
  -}
  case⊥ : ∀ {Γ A}
    → Γ ⊢ `⊥
      ---------
    → Γ ⊢ A

  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
      ----------
    → Γ ⊢ A `⊎ B

  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
      ----------
    → Γ ⊢ A `⊎ B

  case⊎ : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
      ---------
    → Γ ⊢ C

  `tt : ∀ {Γ}
      -------
    → Γ ⊢ `⊤

  case⊤ : ∀{Γ A}
    → Γ ⊢ `⊤ 
    → Γ ⊢ A
    -------
    → Γ ⊢ A

  `[] : ∀{Γ A} 
      ------------
    → Γ ⊢ `List A

  _`∷_ : ∀{Γ A} 
    → Γ ⊢ A
    → Γ ⊢ `List A
      ------------
    → Γ ⊢ `List A

  caseL : ∀{Γ A B} 
    → Γ ⊢ `List A
    → Γ ⊢ B
    → Γ , A , `List A ⊢ B
      --------------------
    → Γ ⊢ B

  `true : ∀{Γ}
      ---------
    → Γ ⊢ `Bool

  `false : ∀{Γ}
      ---------
    → Γ ⊢ `Bool

  _`&&_ : ∀{Γ}
    → Γ ⊢ `Bool
    → Γ ⊢ `Bool
      ----------
    → Γ ⊢ `Bool

  _`||_ : ∀{Γ}
    → Γ ⊢ `Bool
    → Γ ⊢ `Bool
      ----------
    → Γ ⊢ `Bool

  `!_ : ∀{Γ}
    → Γ ⊢ `Bool
      ----------
    → Γ ⊢ `Bool

  caseB : ∀ {Γ A}
    → Γ ⊢ `Bool
    → Γ ⊢ A
    → Γ ⊢ A
      ---------
    → Γ ⊢ A
  

-- Abbreviating de Bruijn indices (unchanged)

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

-- Renaming (new cases in rename).

ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
rename ρ (con n)        =  con n
rename ρ (M `* N)       =  rename ρ M `* rename ρ N
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
rename ρ (case× L M)    =  case× (rename ρ L) (rename (ext (ext ρ)) M)
rename ρ (case⊥ x) = case⊥ (rename ρ x) -- C-c C-a 
rename ρ (`inj₁ x) = `inj₁ (rename ρ x)
rename ρ (`inj₂ x) = `inj₂ (rename ρ x)
rename ρ (case⊎ x x₁ x₂) = case⊎ (rename ρ x) (rename (ext ρ) x₁) (rename (ext ρ) x₂)
{-
  The above case cannot be solved by C-c C-a.
  Goal: Δ ⊢ A
  
  Type Inference:
  (rename ρ x) : Δ ⊢ (A₁ `⊎ B)
  (rename (ext ρ) x₁) : Δ , A₁ ⊢ A
  (rename (ext ρ) x₂) : Δ , B ⊢ A

  To get goal, we need to use "case⊎", which require input types "Δ ⊢ (A₁ `⊎ B)", "Δ , A₁ ⊢ A" and "Δ , B ⊢ A".
  By the finished cases above, we should use "rename" and "ext" to get required types.
  We start by rename, if the type inference is incorrect or failed, we just add "ext" 
  such as "ext ρ" or (ext (ext) ρ) ...
  Then just a few trys we find the answer.
-}
rename ρ `tt = `tt
{-
C-c C-a got wrong answers below!
We need to make sure the basic structure is unchanged.
-}
rename ρ (case⊤ x x₁) = case⊤ (rename ρ x) (rename ρ x₁)
rename ρ `[] = `[]
rename ρ (x `∷ x₁) = (rename ρ x) `∷ (rename ρ x₁)
rename ρ (caseL {a} {b} x x₁ x₂) = caseL (rename ρ x) (rename ρ x₁) (rename (ext (ext ρ)) x₂)
rename ρ `true = `true
rename ρ `false = `false
rename ρ (x `&& x₁) = (rename ρ x) `&&  (rename ρ x₁) 
rename ρ (x `|| x₁) = (rename ρ x) `|| (rename ρ x₁) 
rename ρ (`! x) = `! (rename ρ x) 
rename ρ (caseB x x₁ x₂) = caseB (rename ρ x) (rename ρ x₁) (rename ρ x₂)



-- Substitution (new cases in subst).

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
subst σ (con n)        =  con n
subst σ (M `* N)       =  subst σ M `* subst σ N
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
subst σ (case⊥ x) = case⊥ (subst σ x) -- C-c C-a 
subst σ (`inj₁ x) = `inj₁ (subst σ x)
subst σ (`inj₂ x) = `inj₂ (subst σ x)
subst σ (case⊎ x x₁ x₂) = case⊎ (subst σ x) (subst (exts σ) x₁) (subst (exts σ) x₂) -- similar idea as "rename".
subst σ `tt = `tt
subst σ (case⊤ x x₁) = case⊤ (subst σ x) (subst σ x₁) 
subst σ `[] = `[]
subst σ (x `∷ x₁) = (subst σ x) `∷ (subst σ x₁) 
subst σ (caseL x x₁ x₂) = caseL (subst σ x) (subst σ x₁) (subst (exts (exts σ)) x₂)
subst σ `true = `true
subst σ `false = `false
subst σ (x `&& x₁) = (subst σ x) `&& (subst σ x₁) 
subst σ (x `|| x₁) = (subst σ x) `|| (subst σ x₁) 
subst σ (`! x) = `! (subst σ x)
subst σ (caseB x x₁ x₂) = caseB (subst σ x) (subst σ x₁) (subst σ x₂)
-- Single substitution (unchanged)

_[_] : ∀ {Γ A B}
  → Γ , A ⊢ B
  → Γ ⊢ A
  ------------
  → Γ ⊢ B

_[_] {Γ} {A} N V =  subst {Γ , A} {Γ} σ N
  where
  σ : ∀ {B} → Γ , A ∋ B → Γ ⊢ B
  σ Z      =  V
  σ (S x)  =  ` x

-- Double substitution (needed for alternative product)

_[_][_] : ∀ {Γ A B C}
  → Γ , A , B ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    ---------------
  → Γ ⊢ C

_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ N
  where
  σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x

-- Values (additions for primitive numbers and products)

data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  -- naturals

  V-zero : ∀ {Γ} →
      -----------------
      Value (`zero {Γ})

  V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  -- primitives

  V-con : ∀ {Γ n}
      ---------------------
    → Value {Γ = Γ} (con n)

  -- products

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value `⟨ V , W ⟩

  -- Note the third implicit argument of "`inj₁"
  V-inj₁ : ∀ {Γ A B V}
    → Value V
      ---------------------------
    → Value (`inj₁ {Γ} {A} {B} V) 

  V-inj₂ : ∀ {Γ A B W} 
    → Value W
      ---------------------------
    → Value (`inj₂ {Γ} {A} {B} W) 

  V-⊤ : ∀ {Γ} 
      ---------------
    → Value (`tt {Γ})

  V-[] : ∀ {Γ A} 
      ---------------------
    → Value (`[] {Γ} {A})

  V-∷ : ∀ {Γ A} {V :  Γ ⊢ A} {W :  Γ ⊢ `List A} 
    → Value V
    → Value W
      ----------------
    →  Value (V `∷ W)

  V-true : ∀ {Γ} 
      ---------------------
    → Value (`true {Γ})

  V-false : ∀ {Γ} 
      ---------------------
    → Value (`false {Γ})

-- Reduction (additions for all new features).

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  -- naturals

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  -- fixpoint

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

  -- primitive numbers

  ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
    → L —→ L′
      -----------------
    → L `* M —→ L′ `* M

  ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
    → Value V
    → M —→ M′
      -----------------
    → V `* M —→ V `* M′

  δ-* : ∀ {Γ c d}
      -------------------------------------
    → con {Γ = Γ} c `* con d —→ con (c * d)

  -- let

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ---------------------
    → `let M N —→ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      -------------------
    → `let V N —→ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
    → M —→ M′
      -------------------------
    → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
    → Value V
    → N —→ N′
      -------------------------
    → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

  ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₁ L —→ `proj₁ L′

  ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₂ L —→ `proj₂ L′

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₁ `⟨ V , W ⟩ —→ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₂ `⟨ V , W ⟩ —→ W

  -- alternative formulation of products

  ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
    → L —→ L′
      -----------------------
    → case× L M —→ case× L′ M

  β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
    → Value V
    → Value W
      ----------------------------------
    → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]
  
  -- We need to get implicit argument "Γ" "A" for "case⊥" to suppress warning of "—→" in the last line.
  ξ-case⊥ : ∀ {Γ A L L′}
    → L —→ L′
      -------------------------------------
    → case⊥ {Γ} {A} L —→ case⊥ {Γ} {A} L′

  ξ-inj₁ : ∀{Γ A B M M′}
    → M —→ M′
      -------------------------------------------
    → `inj₁ {Γ} {A} {B} M —→ `inj₁ {Γ} {A} {B} M′ 

  ξ-inj₂ : ∀{Γ A B N N′}
    → N —→ N′
      -------------------------------------------
    → `inj₂ {Γ} {A} {B} N —→ `inj₂ {Γ} {A} {B} N′

  ξ-case⊎ : ∀ {Γ A B C L L′ M N}
    → L —→ L′
        ----------------------------------------------------------
    → case⊎ {Γ} {A} {B} {C} L M N —→ case⊎ {Γ} {A} {B} {C} L′ M N

  -- "β-inj₁" and "β-inj₂" need input evidence "Value" as the examples of "Product".
  β-inj₁ : ∀{Γ A B C M N V}
    → Value V
      ----------------------------------------------
    → case⊎ {Γ} {A} {B} {C} (`inj₁ V) M N —→ M [ V ]

  β-inj₂ : ∀{Γ A B C M N W}
    → Value W
      ----------------------------------------------
    → case⊎ {Γ} {A} {B} {C} (`inj₂ W) M N —→ N [ W ]

  ξ-case⊤ : ∀{Γ A L L′ M}
    → L —→ L′
      ----------------------------------------
    → case⊤ {Γ} {A} L M —→ case⊤ {Γ} {A} L′ M

  β-case⊤ : ∀{Γ A M} 
      -----------------------------
    → case⊤ {Γ} {A} `tt M  —→  M

  ξ-∷₁ : ∀{Γ A M M′}{N : Γ ⊢ `List A}
    → M —→ M′
      -------------------
    → M `∷ N —→ M′ `∷ N

  ξ-∷₂ : ∀{Γ A V} {N N′ : Γ ⊢ `List  A}
    → Value V
    → N —→ N′
      -------------------
    → V `∷ N —→ V `∷ N′

  ξ-caseL : ∀{Γ A B N L L′ M}
    → L —→ L′
      --------------------------------------------------------
    → (caseL {Γ} {A} {B} L M N)  —→ (caseL {Γ} {A} {B} L′ M N) 

  β-[] : ∀{Γ A B M N}
      ----------------------------------
    → (caseL {Γ} {A} {B} `[] M N)  —→ M

  β-∷ : ∀{Γ A B M V W N}
    → Value V
    → Value W
      -------------------------------------------------
    → (caseL {Γ} {A} {B} (V `∷ W) M N)  —→ N [ V ][ W ] 

  ξ-and₁ : ∀{Γ} {L L′ M : Γ ⊢ `Bool}
     → L —→ L′
      ---------------------
     → L `&& M —→ L′ `&&  M

  ξ-and₂ : ∀{Γ} {V M M′ : Γ ⊢ `Bool}
    → Value V
     → M —→ M′
      ---------------------
     → V `&& M —→ V `&&  M′

  β-and-true₁ : ∀ {Γ}
      ------------------------------
    → _`&&_ {Γ} `true `true —→ `true

  β-and-false₁ : ∀ {Γ}
      --------------------------------
    → _`&&_ {Γ} `true `false —→ `false

  β-and-false₂ : ∀ {Γ}
      --------------------------------
    → _`&&_ {Γ} `false `true —→ `false

  β-and-false₃ : ∀ {Γ}
      ---------------------------------
    → _`&&_ {Γ} `false `false —→ `false

  ξ-or₁ : ∀{Γ} {L L′ M : Γ ⊢ `Bool}
     → L —→ L′
      ---------------------
     → L `|| M —→ L′ `||  M

  ξ-or₂ : ∀{Γ} {V M M′ : Γ ⊢ `Bool}
    → Value V
     → M —→ M′
      ---------------------
     → V `|| M —→ V `||  M′

  β-or-true₁ : ∀ {Γ}
      ------------------------------
    → _`||_ {Γ} `true `true —→ `true

  β-or-true₂ : ∀ {Γ}
      -------------------------------
    → _`||_ {Γ} `true `false —→ `true

  β-or-true₃ : ∀ {Γ}
      --------------------------------
    → _`||_ {Γ} `false `true —→ `true

  β-or-false₁ : ∀ {Γ}
      ---------------------------------
    → _`||_ {Γ} `false `false —→ `false

  ξ-not : ∀{Γ} {L L′ : Γ ⊢ `Bool}
     → L —→ L′
      ---------------------
     → `! L —→ `! L′

  β-not-true : ∀ {Γ}
      -----------------------
    → `!_ {Γ} `false —→ `true

  β-not-false : ∀ {Γ}
      -----------------------
    → `!_ {Γ} `true —→ `false
  
  ξ-caseB : ∀{Γ A L L′ M N}
    → L —→ L′
      ----------------------------------------
    → caseB {Γ} {A} L M N —→ caseB {Γ} {A} L′ M N

  β-caseB-true : ∀{Γ A M N} 
      -----------------------------
    → caseB {Γ} {A} `true M N —→ M

  β-caseB-false : ∀{Γ A M N} 
      -----------------------------
    → caseB {Γ} {A} `false M N —→  N
  
  
-- Reflexive/transitive closure (unchanged).

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- Values do not reduce (new cases for products).

V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)

V¬—→ (V-suc VM) (ξ-suc M—→M′)     =  V¬—→ VM M—→M′
V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)    =  V¬—→ VM M—→M′
V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)  =  V¬—→ VN N—→N′
V¬—→ (V-inj₁ x) (ξ-inj₁ x₁) = V¬—→ x x₁
V¬—→ (V-inj₂ x) (ξ-inj₂ x₁) = V¬—→ x x₁
V¬—→ (V-∷ a a₁) (ξ-∷₁ b) = V¬—→ a b
V¬—→ (V-∷ a a₁) (ξ-∷₂ b x) = V¬—→ a₁ x


-- Progress (new cases in theorem).

data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M

progress (ƛ N)                              =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                        =  step (β-ƛ VM)
progress (`zero)                            =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                         =  step (ξ-suc M—→M′)
...    | done VM                            =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                         =  step (ξ-case L—→L′)
...    | done V-zero                        =  step β-zero
...    | done (V-suc VL)                    =  step (β-suc VL)
progress (μ N)                              =  step β-μ
progress (con n)                            =  done V-con
progress (L `* M) with progress L
...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
...    | done V-con with progress M
...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
...        | done V-con                     =  step δ-*
progress (`let M N) with progress M
...    | step M—→M′                         =  step (ξ-let M—→M′)
...    | done VM                            =  step (β-let VM)
progress `⟨ M , N ⟩ with progress M
...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
...    | done VM with progress N
...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
...        | done VN                        =  done (V-⟨ VM , VN ⟩)
progress (`proj₁ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
progress (`proj₂ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
progress (case× L M) with progress L
...    | step L—→L′                         =  step (ξ-case× L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
progress (case⊥ M) with progress M
... | step x = step (ξ-case⊥ x) -- C-c C-a
progress (`inj₁ M) with progress M
... | step x = step (ξ-inj₁ x)
... | done x = done (V-inj₁ x)
progress (`inj₂ M) with progress M
... | step x = step (ξ-inj₂ x)
... | done x = done (V-inj₂ x)
progress (case⊎ M M₁ M₂) with progress M
... | step x = step (ξ-case⊎ x)
... | done (V-inj₁ x) = step (β-inj₁ x)
... | done (V-inj₂ x) = step (β-inj₂ x)
progress `tt = done V-⊤
progress (case⊤ x x₁) with progress x 
... | step x₂ = step (ξ-case⊤ x₂)
... | done V-⊤ = step β-case⊤
progress `[] = done V-[]
progress (x `∷ x₁) with progress x -- progress on the first then the second as the example case of product
... | step x₂ = step (ξ-∷₁ x₂)
... | done x₂ with progress x₁
... | step x₃ = step (ξ-∷₂ x₂ x₃)
... | done x₃ = done (V-∷ x₂ x₃)
progress (caseL x x₁ x₂) with progress x 
... | step x₃ = step (ξ-caseL x₃)
... | done V-[] = step β-[]
... | done (V-∷ x₃ x₄) = step (β-∷ x₃ x₄)
progress `true = done V-true
progress `false = done V-false
progress (x `&& x₁) with progress x 
... | step x₂ = step (ξ-and₁ x₂)
... | done x₂ with progress x₁
... | step x₃ = step (ξ-and₂ x₂ x₃)
... | done x₃ with x₂ | x₃ -- ask x₂ and x₃ to know which β apply
... | V-true | V-true = step β-and-true₁
... | V-true | V-false = step β-and-false₁
... | V-false | V-true = step β-and-false₂
... | V-false | V-false = step β-and-false₃
progress (x `|| x₁) with progress x
... | step x₂ = step (ξ-or₁ x₂)
... | done x₂ with progress x₁ 
... | step x₃ = step (ξ-or₂ x₂ x₃)
... | done x₃ with x₂ | x₃
... | V-true | V-true = step β-or-true₁
... | V-true | V-false = step β-or-true₂
... | V-false | V-true = step β-or-true₃
... | V-false | V-false = step β-or-false₁
progress (`! x) with progress x
... | step x₁ = step (ξ-not x₁)
... | done x₁ with x₁
... | V-true = step β-not-false
... | V-false = step β-not-true
progress (caseB x x₁ x₂) with progress x
... | step x₃ = step (ξ-caseB x₃)
... | done V-true = step β-caseB-true
... | done V-false = step β-caseB-false



-- Evaluation (unchanged).

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N


data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L

eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

compute :  ∀{A} → Gas → (L : ∅ ⊢ A) → ∅ ⊢ A
compute (gas a) L = extract-res (gas a) (eval (gas a) L)
  where
  extract-res : ∀{A} {L : ∅ ⊢ A} → Gas → Steps L → ∅ ⊢ A
  extract-res (gas zero) (steps {p} {q} x x₁) = q
  extract-res (gas (suc amount)) (steps {p} {q} (_ ∎) x₁) = p
  extract-res (gas (suc amount)) (steps (_ —→⟨ x ⟩ x₂) x₁)  = extract-res (gas amount) (steps x₂ x₁)


cube : ∅ ⊢ Nat ⇒ Nat
cube = ƛ (# 0 `* # 0 `* # 0)


-- analogy to "swap×-case"
swap⊎ : ∀ {A B} → ∅ ⊢ A `⊎ B ⇒ B `⊎ A
swap⊎ = ƛ case⊎ (# 0) (`inj₂ (# 0)) (`inj₁ (# 0))

_ : ∀ {B} →  (swap⊎ {`ℕ} {B} · (`inj₁ `zero )) —↠ (`inj₂ `zero)
_ = begin 
      swap⊎ · (`inj₁ `zero ) 
    —→⟨ β-ƛ (V-inj₁ V-zero) ⟩
      case⊎ (`inj₁ `zero ) (`inj₂ (# 0)) (`inj₁ (# 0))
    —→⟨ β-inj₁ V-zero ⟩ 
      (`inj₂ `zero) 
    ∎

to×⊤ : ∀ {A} → ∅ ⊢ A ⇒ A `× `⊤
to×⊤ = ƛ `⟨ (# 0) , `tt ⟩

_ :  compute (gas 100) (to×⊤ · `zero) ≡  `⟨ `zero , `tt ⟩
_ = refl

from×⊤ : ∀ {A} → ∅ ⊢ A `× `⊤ ⇒ A
from×⊤ = ƛ `proj₁ (# 0)

_ : compute (gas 100) (from×⊤ · `⟨ `zero , `tt ⟩) ≡ `zero
_ = refl

from×⊤-case : ∀{A} →  ∅ ⊢ A `× `⊤ ⇒ A
from×⊤-case = ƛ (case× (# 0) (case⊤ (# 0) (# 1)))

_ : compute (gas 100) (from×⊤-case · `⟨ `zero , `tt ⟩) ≡ `zero 
_ = refl

to⊎⊥ : ∀ {A} →  ∅ ⊢ A ⇒ A `⊎ `⊥
to⊎⊥ = ƛ `inj₁ (# 0)

-- only type check
_ = ∅ ⊢  `List (`Bool `⊎ `⊥)
_ = (to⊎⊥ · `true) `∷ ((to⊎⊥ · `false) `∷ `[])

from⊎⊥ : ∀ {A} →  ∅ ⊢ A `⊎ `⊥ ⇒ A
from⊎⊥ = ƛ case⊎ (# 0) (# 0) (case⊥ (# 0))

mapL : ∀{A B} →  ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
mapL = μ ƛ ƛ caseL (# 0) `[] (((# 3) · (# 1)) `∷ ((# 4) · (# 3) · (# 0)))

--type check
_ = ∅ ⊢  `List `Bool
_ = mapL · from⊎⊥ · (to⊎⊥ · `true) `∷ ((to⊎⊥ · `false) `∷ `[])

--convertion check
_ : compute (gas 100) 
  (mapL · from⊎⊥ · (to⊎⊥ · `true) `∷ ((to⊎⊥ · `false) `∷ `[])) ≡ (`true `∷ (`false `∷ `[]))
_ = refl

{-
reduceL : ∅ ⊢ (A ⇒ A ⇒ B) ⇒ B ⇒  `List A ⇒ B
reduceL = μ rL ⇒ ƛ f ⇒ ƛ b ⇒ ƛ xs ⇒
         caseL xs
           [[]⇒ b
           | x ∷ xs ⇒  rL · f · (f · x · b) · xs ]

bool⊎con-to-con : ∅ ⊢ (`Bool `⊎ `ℕ)  ⇒ `ℕ 
bool⊎con-to-con = ƛ s ⇒ 
          case⊎ s
           [inj₁ b ⇒ caseB b [`true ⇒ con 1 | `false ⇒ con 0]
           | inj₂ con x ⇒  con x ]

mul-bool×con : ∅ ⊢ `Bool `× Nat  ⇒ Nat 
mul-bool×con = ƛ p ⇒ caseB (proj₁ p) [`true ⇒ (proj₂ p) | `false ⇒ con 0]
-}
reduceL : ∀{A B} →  ∅ ⊢ (A ⇒ B ⇒ B) ⇒ B ⇒ `List A ⇒ B
reduceL = μ ƛ ƛ ƛ caseL (# 0) (# 1) ((# 5) · (# 4) · ((# 4) · (# 1) · (# 3)) · (# 0))

mul : ∅ ⊢ Nat ⇒ Nat ⇒ Nat 
mul = ƛ ƛ (# 0) `* (# 1)

_ : compute (gas 100) 
    (reduceL · mul · con 1 ·  (con 2 `∷ (con 1011 `∷ `[]))) ≡ con 2022
_ = refl

bool⊎con-to-con : ∅ ⊢ (`Bool `⊎ Nat)  ⇒ Nat 
bool⊎con-to-con = ƛ case⊎ (# 0) (caseB (# 0) (con 1) (con 0)) (# 0)

mul-bool×con : ∅ ⊢ `Bool `× Nat  ⇒ Nat 
mul-bool×con = ƛ caseB (`proj₁ (# 0)) (`proj₂ (# 0)) (con 0)

_ : compute (gas 100) 
  (mapL · bool⊎con-to-con · 
    ((`inj₁ `false) `∷ ((`inj₂ (con 2)) `∷ ((`inj₁ `true) `∷ `[])))) ≡ (con 0 `∷ (con 2 `∷ (con 1 `∷ `[])))
_ = refl

_ : compute (gas 100)
  (mapL · mul-bool×con · (`⟨ `false , con 2020 ⟩  `∷ (`⟨ `false , con 2021 ⟩ `∷ (`⟨ `true , con 2022 ⟩ `∷ `[])))) ≡
    (con 0 `∷ (con 0 `∷ (con 2022 `∷ `[])))
_ = refl

_ : compute (gas 100) 
  (mapL · cube · (con 2 `∷ (con 3 `∷ (con 5 `∷ `[])))) ≡ (con 8 `∷ (con 27 `∷ (con 125 `∷ `[]))) 
_ = refl

{-
We construct a bool expression and check its bool table.
a b c   (!a && b) || c   
0 0 0         0
0 0 1         1
0 1 0         1
0 1 1         1
1 0 0         0
1 0 1         1
1 1 0         0
1 1 1         1

And we can see the Result below matches the expected bool table.

(correspond java code for computing bool table:
  public static void main(String[] args) {
    boolean[] bs = new boolean[]{false, true};
    for(var a : bs){
      for(var b : bs){
        for(var c : bs){
          System.out.println(((!a) && b) || c);
        }
      }
    }
  }
)
-}

bool-expression1 : ∅ ⊢ `Bool ⇒ `Bool ⇒ `Bool ⇒ `Bool
bool-expression1 = ƛ ƛ ƛ ((`! (# 2)) `&& (# 1)) `|| (# 0)

_ : compute (gas 100) 
  (bool-expression1 · `false · `false · `false) ≡ `false
_ = refl

_ : compute (gas 100) 
  (bool-expression1 · `false · `false · `true) ≡ `true
_ = refl

_ : compute (gas 100) 
  (bool-expression1 · `false · `true · `false) ≡ `true
_ = refl

_ : compute (gas 100) 
  (bool-expression1 · `false · `true · `true) ≡ `true
_ = refl

_ : compute (gas 100) 
  (bool-expression1 · `true · `false · `false) ≡ `false
_ = refl

_ : compute (gas 100) 
  (bool-expression1 · `true · `false · `true) ≡ `true
_ = refl

_ : compute (gas 100) 
  (bool-expression1 · `true · `true · `false) ≡ `false
_ = refl

_ : compute (gas 100) 
  (bool-expression1 · `true · `true · `true) ≡ `true 
_ = refl 