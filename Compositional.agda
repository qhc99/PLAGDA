open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import plfa.part2.Untyped
  using (Context; _,_; ★; _∋_; _⊢_; `_; ƛ_; _·_)
open import plfa.part3.Denotational
  using (Value; _↦_; _`,_; _⊔_; ⊥; _⊑_; _⊢_↓_;
         ⊑-bot; ⊑-fun; ⊑-conj-L; ⊑-conj-R1; ⊑-conj-R2;
         ⊑-dist; ⊑-refl; ⊑-trans; ⊔↦⊔-dist;
         var; ↦-intro; ↦-elim; ⊔-intro; ⊥-intro; sub;
         up-env; ℰ; _≃_; ≃-sym; Denotation; Env)
open plfa.part3.Denotational.≃-Reasoning

ℱ : ∀{Γ} → Denotation (Γ , ★) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)