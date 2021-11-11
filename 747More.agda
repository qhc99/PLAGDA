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

-- Types (third and fourth are new).

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Nat   : Type
  _`×_  : Type → Type → Type
  `⊥   : Type
  _`⊎_  : Type → Type → Type
  `⊤    : Type
  `⊤′    : Type
  `List_ : Type → Type

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
  We see how the typing rule of "Alternative formulation of products" is transformed 
  into "case×" above and we get "case⊥" by analogy.
  It means we can get any type if we have type "Empty".
  -}
  case⊥ : ∀ {Γ A}
    → Γ ⊢ `⊥
    ---------
    → Γ ⊢ A

  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ A `⊎ B

  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
    → Γ ⊢ A `⊎ B

  case⊎ : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
      ---------
    → Γ ⊢ C

  `tt : ∀ {Γ}
    ---------
    → Γ ⊢ `⊤

  `tt′ : ∀ {Γ}
    ---------
    → Γ ⊢ `⊤′ 

  case⊤ : ∀{Γ A}
    → Γ ⊢ `⊤′ 
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
  We start by rename, if the type inference is incorrect or failed, we just "ext ρ".
  Then just a few trys we find the answer.
-}
rename ρ `tt = `tt
rename ρ `tt′ = `tt′
rename ρ (case⊤ x x₁) = rename ρ x₁
rename ρ `[] = `[]
rename ρ (x `∷ x₁) = rename ρ x₁
rename ρ (caseL x x₁ x₂) = rename ρ x₁



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
subst σ `tt′ = `tt′
subst σ (case⊤ x x₁) = subst σ x₁
subst σ `[] = `[]
subst σ (x `∷ x₁) = subst σ x₁
subst σ (caseL x x₁ x₂) = subst σ x₁
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

_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ′ N
  where
  σ′ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ′ Z          =  W
  σ′ (S Z)      =  V
  σ′ (S (S x))  =  ` x

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
  V-inj₁ : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
      ---------------------------
    → Value (`inj₁ {Γ} {A} {B} V) 

  V-inj₂ : ∀ {Γ A B} {W : Γ ⊢ B}
    → Value W
      ---------------------------
    → Value (`inj₂ {Γ} {A} {B} W) 

  V-⊤ : ∀ {Γ} 
      ---------------
    → Value (`tt {Γ})

  V-⊤′ : ∀ {Γ} 
      ---------------
    → Value (`tt′ {Γ})

  V-[] : ∀ {Γ A} 
      ---------------------
    → Value (`[] {Γ} {A})

  -- need specify types of V and W to suppress warning
  V-∷ : ∀ {Γ A} {V :  Γ ⊢ A} {W :  Γ ⊢ `List A} 
    → Value V
    → Value W
      ----------------
    →  Value (V `∷ W)

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
  ξ-case⊥ : ∀ {Γ A} {L L′ : Γ ⊢ `⊥}
    → L —→ L′
      -------------------------------------
    → case⊥ {Γ} {A} L —→ case⊥ {Γ} {A} L′

  ξ-inj₁ : ∀{Γ A B} {M M′ : Γ ⊢ A}
    → M —→ M′
      -------------------------------------------
    → `inj₁ {Γ} {A} {B} M —→ `inj₁ {Γ} {A} {B} M′ 

  ξ-inj₂ : ∀{Γ A B} {N N′ : Γ ⊢ B}
    → N —→ N′
      -------------------------------------------
    → `inj₂ {Γ} {A} {B} N —→ `inj₂ {Γ} {A} {B} N′

  ξ-case⊎ : ∀ {Γ A B C I1 I2} {L L′ : Γ ⊢ A `⊎ B}
    → L —→ L′
        -------------------------------------------------------------
    → case⊎ {Γ} {A} {B} {C} L I1 I2 —→ case⊎ {Γ} {A} {B} {C} L′ I1 I2

  β-inj₁ : ∀{Γ A B C M N V}
      ----------------------------------------------
    → case⊎ {Γ} {A} {B} {C} (`inj₁ V) M N —→ M [ V ]

  β-inj₂ : ∀{Γ A B C M N W}
      ----------------------------------------------
    → case⊎ {Γ} {A} {B} {C} (`inj₂ W) M N —→ N [ W ]

  ξ-case⊤ : ∀{Γ A M} {L L′ : Γ ⊢ `⊤′}
    → L —→ L′
      ----------------------------------------
    → case⊤ {Γ} {A} L M —→ case⊤ {Γ} {A} L′ M

  β-case⊤ : ∀{Γ A M} 
      -----------------------------
    → (case⊤ {Γ} {A} `tt′ M ) —→  M

  ξ-∷₁ : ∀{Γ A M M′}{N : Γ ⊢ `List A}
    → M —→ M′
      -------------------
    → M `∷ N —→ M′ `∷ N

  ξ-∷₂ : ∀{Γ A V} {N N′ : Γ ⊢ `List  A}
    → N —→ N′
      -------------------
    → V `∷ N —→ V `∷ N′

  ξ-caseL : ∀{Γ A B N} {L L′ : Γ ⊢ `List A} {M : Γ ⊢ B} 
    → L —→ L′
      ----------------------------
    → (caseL L M N)  —→ (caseL L′ M N) 

  β-[] : ∀{Γ A B M} {N : Γ , A , `List A ⊢ B} 
      ---------------------------------------
    → caseL `[] M N  —→ M

  β-∷ : ∀{Γ A B M V W} {N : Γ , A , `List A ⊢ B} 
      ------------------------------------
    → caseL (V `∷ W) M N  —→ N [ V ][ W ] 
  
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
V¬—→ (V-∷ a a₁) (ξ-∷₂ b) = V¬—→ a₁ b


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
... | done (V-inj₁ x) = step β-inj₁ -- case split then solved by C-c C-a
... | done (V-inj₂ x) = step β-inj₂
progress `tt = done V-⊤
progress `tt′ = done V-⊤′
progress (case⊤ x x₁) with progress x 
... | step x₂ = step (ξ-case⊤ x₂)
... | done V-⊤′ = step β-case⊤
progress `[] = done V-[]
progress (x `∷ x₁) with progress x | progress x₁ -- progress on x and x₁ instead of progress on x₁ only.
... | step x₂ | step x₃ = step (ξ-∷₁ x₂)
... | step x₂ | done x₃ = step (ξ-∷₁ x₂)
... | done x₂ | step x₃ = step (ξ-∷₂ x₃)
... | done x₂ | done x₃ = done (V-∷ x₂ x₃)
progress (caseL x x₁ x₂) with progress x
... | step x₃ = step (ξ-caseL x₃)
... | done V-[] = step β-[]
... | done (V-∷ x₃ x₄) = step β-∷



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

cube : ∅ ⊢ Nat ⇒ Nat
cube = ƛ (# 0 `* # 0 `* # 0)

{-
_ : cube · con 2 —↠ con 8
_ =
  begin
    cube · con 2
  —→⟨ β-ƛ V-con ⟩
    con 2 `* con 2 `* con 2
  —→⟨ ξ-*₁ δ-* ⟩
    con 4 `* con 2
  —→⟨ δ-* ⟩
    con 8
  ∎
-}

exp10 : ∅ ⊢ Nat ⇒ Nat
exp10 = ƛ (`let (# 0 `* # 0)
            (`let (# 0 `* # 0)
              (`let (# 0 `* # 2)
                (# 0 `* # 0))))

{-
_ : exp10 · con 2 —↠ con 1024
_ =
  begin
    exp10 · con 2
  —→⟨ β-ƛ V-con ⟩
    `let (con 2 `* con 2) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ ξ-let δ-* ⟩
    `let (con 4) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ β-let V-con ⟩
    `let (con 4 `* con 4) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ ξ-let δ-* ⟩
    `let (con 16) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ β-let V-con ⟩
    `let (con 16 `* con 2) (# 0 `* # 0)
  —→⟨ ξ-let δ-* ⟩
    `let (con 32) (# 0 `* # 0)
  —→⟨ β-let V-con ⟩
    con 32 `* con 32
  —→⟨ δ-* ⟩
    con 1024
  ∎
-}

swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap× = ƛ `⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩

{-
_ : swap× · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
    swap× · `⟨ con 42 , `zero ⟩
  —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
    `⟨ `proj₂ `⟨ con 42 , `zero ⟩ , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₁ (β-proj₂ V-con V-zero) ⟩
    `⟨ `zero , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₂ V-zero (β-proj₁ V-con V-zero) ⟩
    `⟨ `zero , con 42 ⟩
  ∎
-}

swap×-case : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap×-case = ƛ case× (# 0) `⟨ # 0 , # 1 ⟩

{-
_ : swap×-case · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
     swap×-case · `⟨ con 42 , `zero ⟩
   —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
     case× `⟨ con 42 , `zero ⟩ `⟨ # 0 , # 1 ⟩
   —→⟨ β-case× V-con V-zero ⟩
     `⟨ `zero , con 42 ⟩
   ∎
-}

-- analogy to "swap×-case"
swap⊎ : ∀ {A B} → ∅ ⊢ A `⊎ B ⇒ B `⊎ A
swap⊎ = ƛ case⊎ (# 0) (`inj₂ (# 0)) (`inj₁ (# 0))

_ : ∀ {B} →  (swap⊎ {`ℕ} {B} · (`inj₁ `zero )) —↠ (`inj₂ `zero)
_ = begin 
      swap⊎ · (`inj₁ `zero ) 
    —→⟨ β-ƛ (V-inj₁ V-zero) ⟩
      case⊎ (`inj₁ `zero ) (`inj₂ (# 0)) (`inj₁ (# 0))
    —→⟨ β-inj₁ ⟩ 
      (`inj₂ `zero) 
    ∎

-- 747/PLFA exercise: SumsEmpty (10 points)
-- Add sums and the empty type to the above, using the syntax and rules
-- given in PLFA More. If you want extra practice, add lists.
-- Include examples of computations for each new feature.

-- Hint: do these one at a time. Start with the empty type.
-- For each section in the file, think whether something has to be added, and what.
-- If you add constructors to an inductive datatype, loading the file
-- will helpfully tell you what cases are missing in code using it, and where.

-- PLFA exercise (STRETCH):
{-
double-subst :
  ∀ {Γ} {A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} →
    N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
double-subst {Γ} {A} {B} {C} {V} {W} {N} = {! !} 
-}
  