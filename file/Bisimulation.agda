open import plfa.part2.More
open import 747Decidable using (Dec; yes; no)
open import 747Isomorphism using (_⇔_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) 
open import 747Connectives using (_×_)

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†


eq-† : ∀{Γ A N} {M M† : Γ ⊢ A} → M ~ M† → (M† ≡ N) ⇔ (M ~ N)
eq-† {Γ} {A} {N} {M} {M†} m~m† = record { to = eq-†-to ; from = eq-†-from } 
  where
  eq-†-to : M† ≡ N → M ~ N
  eq-†-to refl = m~m†

  eq-†-from : M ~ N → M† ≡ N
  eq-†-from m~n = {!   !}

~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val ~`           ()
~val (~ƛ ~N)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()

~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
    --------
  → Value M
~val⁻¹ = {!   !}

~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)

~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)

~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)

~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~M
  ~σ (S x)  =  ~`

data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N

sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg  M† N
sim ~`              ()
sim (~ƛ ~N)         ()
sim (~L ~· ~M)      (ξ-·₁ L—→)
  with sim ~L L—→
...  | leg ~L′ L†—→                 =  leg (~L′ ~· ~M)   (ξ-·₁ L†—→)
sim (~V ~· ~M)      (ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
sim (~let ~M ~N)    (ξ-let M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
sim (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
  
sim⁻¹ : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → Leg  M† N
  → (M ~ M†) × (M —→ N)
sim⁻¹ l = {!   !}