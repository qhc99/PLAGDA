module PropertiesRefactor where

-- Library

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Agda.Builtin.Bool using (true; false)
open import Function using (_∘_)
open import LambdaDefs

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-suc vm) (ξ-suc msn) = V¬—→ vm msn

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V msn vm = V¬—→ vm msn


infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ


canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A

canonical (⊢ƛ v:a) V-ƛ = C-ƛ v:a
canonical ⊢zero V-zero = C-zero
canonical (⊢suc v:a) (V-suc vv) = C-suc (canonical v:a vv)


value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value (C-ƛ x) = V-ƛ
value C-zero = V-zero
value (C-suc cm:a) = V-suc (value cm:a)


typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ x) = ⊢ƛ x
typed C-zero = ⊢zero
typed (C-suc cm:a) = ⊢suc (typed cm:a)


data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢ƛ m:a) = done V-ƛ
progress (m:a · m:a₁) with progress m:a
... | step x = step (ξ-·₁ x)
... | done x with progress m:a₁
... | step x₁ = step (ξ-·₂ x x₁)
... | done x₁ with canonical m:a x
... | C-ƛ x₂ = step (β-ƛ x₁)
progress ⊢zero = done V-zero
progress (⊢suc m:a) with progress m:a
... | step x = step (ξ-suc x)
... | done x = done (V-suc x)
progress (⊢case m:a m:a₁ m:a₂) with progress m:a
... | step x = step (ξ-case x)
... | done x with canonical m:a x
... | C-zero = step β-zero
... | C-suc cv = step (β-suc (value cv))
progress (⊢μ m:a) = step β-μ

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z = Z
ext ρ (S x lj) = S x (ρ lj)

rename : ∀ {Γ Δ}
        → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
          ----------------------------------
        → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)

rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C

drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C

swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B

subst {x = x₂} v:a (⊢` {x = .x₂} Z) with x₂ ≟ x₂
... | .true because ofʸ refl = weaken v:a
... | .false because ofⁿ ¬p = ⊥-elim (¬p refl)
subst {x = x₂} v:a (⊢` {x = x₁} (S x x₃)) with x₁ ≟ x₂
... | .true because ofʸ refl = ⊥-elim (x refl)
... | .false because ofⁿ ¬p = ⊢` x₃
subst {x = x₁} v:a (⊢ƛ {x = x} n:b) with x ≟ x₁
... | .true because ofʸ refl = ⊢ƛ (drop n:b)
... | .false because ofⁿ ¬p = ⊢ƛ (subst v:a (swap ¬p n:b))
subst v:a (n:b · n:b₁) = (subst v:a n:b) · (subst v:a n:b₁)
subst v:a ⊢zero = ⊢zero
subst v:a (⊢suc n:b) = ⊢suc (subst v:a n:b)
subst {x = x₁} v:a (⊢case {x = x} n:b n:b₁ n:b₂) with x ≟ x₁
... | .true because ofʸ refl = ⊢case (subst v:a n:b) (subst v:a n:b₁) (drop n:b₂)
... | .false because ofⁿ ¬p = ⊢case (subst v:a n:b) (subst v:a n:b₁) (subst v:a (swap ¬p n:b₂))
subst {x = x₁} v:a (⊢μ {x = x} n:b) with x ≟ x₁
... | .true because ofʸ refl = ⊢μ (drop n:b)
... | .false because ofⁿ ¬p = ⊢μ (subst v:a (swap ¬p n:b))

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A

preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M

sucμ  =  μ "x" ⇒ `suc (` "x")


record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N

data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N  
    → Finished N
      ----------
    → Steps L

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M
