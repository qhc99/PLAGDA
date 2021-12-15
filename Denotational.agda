open import Agda.Primitive using (lzero; lsuc)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)
open import plfa.part2.Untyped
  using (Context; ★; _∋_; ∅; _,_; Z; S_; _⊢_; `_; _·_; ƛ_;
         #_; twoᶜ; ext; rename; exts; subst; subst-zero; _[_])
open import plfa.part2.Substitution using (Rename; extensionality; rename-id)

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-bot : ∀ {v} → ⊥ ⊑ v

  ⊑-conj-L : ∀ {u v w}
    → v ⊑ u
    → w ⊑ u
      -----------
    → (v ⊔ w) ⊑ u

  ⊑-conj-R1 : ∀ {u v w}
    → u ⊑ v
      -----------
    → u ⊑ (v ⊔ w)

  ⊑-conj-R2 : ∀ {u v w}
    → u ⊑ w
      -----------
    → u ⊑ (v ⊔ w)

  ⊑-trans : ∀ {u v w}
    → u ⊑ v
    → v ⊑ w
      -----
    → u ⊑ w

  ⊑-fun : ∀ {v w v′ w′}
    → v′ ⊑ v
    → w ⊑ w′
      -------------------
    → (v ↦ w) ⊑ (v′ ↦ w′)

  ⊑-dist : ∀{v w w′}
      ---------------------------------
    → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

⊑-refl : ∀ {v} → v ⊑ v
⊑-refl {⊥} = ⊑-bot
⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

⊔⊑⊔ : ∀ {v w v′ w′}
  → v ⊑ v′  →  w ⊑ w′
    -----------------------
  → (v ⊔ w) ⊑ (v′ ⊔ w′)
⊔⊑⊔ d₁ d₂ = ⊑-conj-L (⊑-conj-R1 d₁) (⊑-conj-R2 d₂)

⊔↦⊔-dist : ∀{v v′ w w′ : Value}
  → (v ⊔ v′) ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v′ ↦ w′)
⊔↦⊔-dist = ⊑-trans ⊑-dist (⊔⊑⊔ (⊑-fun (⊑-conj-R1 ⊑-refl) ⊑-refl)
                            (⊑-fun (⊑-conj-R2 ⊑-refl) ⊑-refl))


⊔⊑-invL : ∀{u v w : Value}
  → u ⊔ v ⊑ w
    ---------
  → u ⊑ w
⊔⊑-invL (⊑-conj-L lt1 lt2) = lt1
⊔⊑-invL (⊑-conj-R1 lt) = ⊑-conj-R1 (⊔⊑-invL lt)
⊔⊑-invL (⊑-conj-R2 lt) = ⊑-conj-R2 (⊔⊑-invL lt)
⊔⊑-invL (⊑-trans lt1 lt2) = ⊑-trans (⊔⊑-invL lt1) lt2

⊔⊑-invR : ∀{u v w : Value}
  → u ⊔ v ⊑ w
    ---------
  → v ⊑ w
⊔⊑-invR (⊑-conj-L lt1 lt2) = lt2
⊔⊑-invR (⊑-conj-R1 lt) = ⊑-conj-R1 (⊔⊑-invR lt)
⊔⊑-invR (⊑-conj-R2 lt) = ⊑-conj-R2 (⊔⊑-invR lt)
⊔⊑-invR (⊑-trans lt1 lt2) = ⊑-trans (⊔⊑-invR lt1) lt2

Env : Context → Set
Env Γ = ∀ (x : Γ ∋ ★) → Value

`∅ : Env ∅
`∅ ()

infixl 5 _`,_

_`,_ : ∀ {Γ} → Env Γ → Value → Env (Γ , ★)
(γ `, v) Z = v
(γ `, v) (S x) = γ x

init : ∀ {Γ} → Env (Γ , ★) → Env Γ
init γ x = γ (S x)

last : ∀ {Γ} → Env (Γ , ★) → Value
last γ = γ Z

init-last : ∀ {Γ} → (γ : Env (Γ , ★)) → γ ≡ (init γ `, last γ)
init-last {Γ} γ = extensionality lemma
  where lemma : ∀ (x : Γ , ★ ∋ ★) → γ x ≡ (init γ `, last γ) x
        lemma Z      =  refl
        lemma (S x)  =  refl

_`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
_`⊑_ {Γ} γ δ = ∀ (x : Γ ∋ ★) → γ x ⊑ δ x

`⊥ : ∀ {Γ} → Env Γ
`⊥ x = ⊥

_`⊔_ : ∀ {Γ} → Env Γ → Env Γ → Env Γ
(γ `⊔ δ) x = γ x ⊔ δ x

`⊑-refl : ∀ {Γ} {γ : Env Γ} → γ `⊑ γ
`⊑-refl {Γ} {γ} x = ⊑-refl {γ x}

⊑-env-conj-R1 : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → γ `⊑ (γ `⊔ δ)
⊑-env-conj-R1 γ δ x = ⊑-conj-R1 ⊑-refl

⊑-env-conj-R2 : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → δ `⊑ (γ `⊔ δ)
⊑-env-conj-R2 γ δ x = ⊑-conj-R2 ⊑-refl

infix 3 _⊢_↓_

data _⊢_↓_ : ∀{Γ} → Env Γ → (Γ ⊢ ★) → Value → Set where

  var : ∀ {Γ} {γ : Env Γ} {x}
      ---------------
    → γ ⊢ (` x) ↓ γ x

  ↦-elim : ∀ {Γ} {γ : Env Γ} {L M v w}
    → γ ⊢ L ↓ (v ↦ w)
    → γ ⊢ M ↓ v
      ---------------
    → γ ⊢ (L · M) ↓ w

  ↦-intro : ∀ {Γ} {γ : Env Γ} {N v w}
    → γ `, v ⊢ N ↓ w
      -------------------
    → γ ⊢ (ƛ N) ↓ (v ↦ w)

  ⊥-intro : ∀ {Γ} {γ : Env Γ} {M}
      ---------
    → γ ⊢ M ↓ ⊥

  ⊔-intro : ∀ {Γ} {γ : Env Γ} {M v w}
    → γ ⊢ M ↓ v
    → γ ⊢ M ↓ w
      ---------------
    → γ ⊢ M ↓ (v ⊔ w)

  sub : ∀ {Γ} {γ : Env Γ} {M v w}
    → γ ⊢ M ↓ v
    → w ⊑ v
      ---------
    → γ ⊢ M ↓ w

id : ∅ ⊢ ★
id = ƛ # 0

denot-id1 : ∀ {γ} → γ ⊢ id ↓ ⊥ ↦ ⊥
denot-id1 = ↦-intro var

denot-id2 : ∀ {γ} → γ ⊢ id ↓ (⊥ ↦ ⊥) ↦ (⊥ ↦ ⊥)
denot-id2 = ↦-intro var

denot-id3 : `∅ ⊢ id ↓ (⊥ ↦ ⊥) ⊔ (⊥ ↦ ⊥) ↦ (⊥ ↦ ⊥)
denot-id3 = ⊔-intro denot-id1 denot-id2

denot-twoᶜ : ∀{u v w : Value} → `∅ ⊢ twoᶜ ↓ ((u ↦ v ⊔ v ↦ w) ↦ u ↦ w)
denot-twoᶜ {u}{v}{w} =
  ↦-intro (↦-intro (↦-elim (sub var lt1) (↦-elim (sub var lt2) var)))
  where lt1 : v ↦ w ⊑ u ↦ v ⊔ v ↦ w
        lt1 = ⊑-conj-R2 (⊑-fun ⊑-refl ⊑-refl)

        lt2 : u ↦ v ⊑ u ↦ v ⊔ v ↦ w
        lt2 = (⊑-conj-R1 (⊑-fun ⊑-refl ⊑-refl))

Δ : ∅ ⊢ ★
Δ = (ƛ (# 0) · (# 0))

denot-Δ : ∀ {v w} → `∅ ⊢ Δ ↓ ((v ↦ w ⊔ v) ↦ w)
denot-Δ = ↦-intro (↦-elim (sub var (⊑-conj-R1 ⊑-refl))
                          (sub var (⊑-conj-R2 ⊑-refl)))

Ω : ∅ ⊢ ★
Ω = Δ · Δ

denot-Ω : `∅ ⊢ Ω ↓ ⊥
denot-Ω = ↦-elim denot-Δ (⊔-intro (↦-intro ⊥-intro) ⊥-intro)

denot-Ω' : `∅ ⊢ Ω ↓ ⊥
denot-Ω' = ⊥-intro

↦-elim2 : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v₁ v₂ v₃}
  → γ ⊢ M₁ ↓ (v₁ ↦ v₃)
  → γ ⊢ M₂ ↓ v₂
  → v₁ ⊑ v₂
    ------------------
  → γ ⊢ (M₁ · M₂) ↓ v₃
↦-elim2 d₁ d₂ lt = ↦-elim d₁ (sub d₂ lt)

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

Denotation : Context → Set₁
Denotation Γ = (Env Γ → Value → Set)

ℰ : ∀{Γ} → (M : Γ ⊢ ★) → Denotation Γ
ℰ M = λ γ v → γ ⊢ M ↓ v

infix 3 _≃_

_≃_ : ∀ {Γ} → (Denotation Γ) → (Denotation Γ) → Set
(_≃_ {Γ} D₁ D₂) = (γ : Env Γ) → (v : Value) → D₁ γ v iff D₂ γ v

≃-refl : ∀ {Γ : Context} → {M : Denotation Γ}
  → M ≃ M
≃-refl γ v = ⟨ (λ x → x) , (λ x → x) ⟩

≃-sym : ∀ {Γ : Context} → {M N : Denotation Γ}
  → M ≃ N
    -----
  → N ≃ M
≃-sym eq γ v = ⟨ (proj₂ (eq γ v)) , (proj₁ (eq γ v)) ⟩

≃-trans : ∀ {Γ : Context} → {M₁ M₂ M₃ : Denotation Γ}
  → M₁ ≃ M₂
  → M₂ ≃ M₃
    -------
  → M₁ ≃ M₃
≃-trans eq1 eq2 γ v = ⟨ (λ z → proj₁ (eq2 γ v) (proj₁ (eq1 γ v) z)) ,
                        (λ z → proj₂ (eq1 γ v) (proj₂ (eq2 γ v) z)) ⟩

module ≃-Reasoning {Γ : Context} where

  infix  1 start_
  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _☐

  start_ : ∀ {x y : Denotation Γ}
    → x ≃ y
      -----
    → x ≃ y
  start x≃y  =  x≃y

  _≃⟨_⟩_ : ∀ (x : Denotation Γ) {y z : Denotation Γ}
    → x ≃ y
    → y ≃ z
      -----
    → x ≃ z
  (x ≃⟨ x≃y ⟩ y≃z) =  ≃-trans x≃y y≃z

  _≃⟨⟩_ : ∀ (x : Denotation Γ) {y : Denotation Γ}
    → x ≃ y
      -----
    → x ≃ y
  x ≃⟨⟩ x≃y  =  x≃y

  _☐ : ∀ (x : Denotation Γ)
      -----
    → x ≃ x
  (x ☐)  =  ≃-refl

ext-⊑ : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
    ------------------------------
  → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
ext-⊑ ρ lt Z = ⊑-refl
ext-⊑ ρ lt (S n′) = lt n′

rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
  → γ ⊢ M ↓ v
    ---------------------
  → δ ⊢ (rename ρ M) ↓ v
rename-pres ρ lt (var {x = x}) = sub var (lt x)
rename-pres ρ lt (↦-elim d d₁) =
   ↦-elim (rename-pres ρ lt d) (rename-pres ρ lt d₁)
rename-pres ρ lt (↦-intro d) =
   ↦-intro (rename-pres (ext ρ) (ext-⊑ ρ lt) d)
rename-pres ρ lt ⊥-intro = ⊥-intro
rename-pres ρ lt (⊔-intro d d₁) =
   ⊔-intro (rename-pres ρ lt d) (rename-pres ρ lt d₁)
rename-pres ρ lt (sub d lt′) =
   sub (rename-pres ρ lt d) lt′

⊑-env : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
  → γ ⊢ M ↓ v
  → γ `⊑ δ
    ----------
  → δ ⊢ M ↓ v
⊑-env{Γ}{γ}{δ}{M}{v} d lt
      with rename-pres{Γ}{Γ}{v}{γ}{δ}{M} (λ {A} x → x) lt d
... | δ⊢id[M]↓v rewrite rename-id {Γ}{★}{M} =
      δ⊢id[M]↓v

up-env : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
  → (γ `, u₁) ⊢ M ↓ v
  → u₁ ⊑ u₂
    -----------------
  → (γ `, u₂) ⊢ M ↓ v
up-env d lt = ⊑-env d (ext-le lt)
  where
  ext-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
  ext-le lt Z = lt
  ext-le lt (S n) = ⊑-refl

infix 5 _∈_

_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ v ↦ w = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w

infix 5 _⊆_

_⊆_ : Value → Value → Set
v ⊆ w = ∀{u} → u ∈ v → u ∈ w

∈→⊑ : ∀{u v : Value}
    → u ∈ v
      -----
    → u ⊑ v
∈→⊑ {.⊥} {⊥} refl = ⊑-bot
∈→⊑ {v ↦ w} {v ↦ w} refl = ⊑-refl
∈→⊑ {u} {v ⊔ w} (inj₁ x) = ⊑-conj-R1 (∈→⊑ x)
∈→⊑ {u} {v ⊔ w} (inj₂ y) = ⊑-conj-R2 (∈→⊑ y)

⊆→⊑ : ∀{u v : Value}
    → u ⊆ v
      -----
    → u ⊑ v
⊆→⊑ {⊥} s with s {⊥} refl
... | x = ⊑-bot
⊆→⊑ {u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u ⊔ u′} s = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))

⊔⊆-inv : ∀{u v w : Value}
       → (u ⊔ v) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = ⟨ (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x)) ⟩

↦⊆→∈ : ∀{v w u : Value}
     → v ↦ w ⊆ u
       ---------
     → v ↦ w ∈ u
↦⊆→∈ incl = incl refl

data Fun : Value → Set where
  fun : ∀{u v w} → u ≡ (v ↦ w) → Fun u

all-funs : Value → Set
all-funs v = ∀{u} → u ∈ v → Fun u

¬Fun⊥ : ¬ (Fun ⊥)
¬Fun⊥ (fun ())

all-funs∈ : ∀{u}
      → all-funs u
      → Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ∈ u
all-funs∈ {⊥} f with f {⊥} refl
... | fun ()
all-funs∈ {v ↦ w} f = ⟨ v , ⟨ w , refl ⟩ ⟩
all-funs∈ {u ⊔ u′} f
    with all-funs∈ (λ z → f (inj₁ z))
... | ⟨ v , ⟨ w , m ⟩ ⟩ = ⟨ v , ⟨ w , (inj₁ m) ⟩ ⟩

⨆dom : (u : Value) → Value
⨆dom ⊥  = ⊥
⨆dom (v ↦ w) = v
⨆dom (u ⊔ u′) = ⨆dom u ⊔ ⨆dom u′

⨆cod : (u : Value) → Value
⨆cod ⊥  = ⊥
⨆cod (v ↦ w) = w
⨆cod (u ⊔ u′) = ⨆cod u ⊔ ⨆cod u′

↦∈→⊆⨆dom : ∀{u v w : Value}
          → all-funs u  →  (v ↦ w) ∈ u
            ----------------------
          → v ⊆ ⨆dom u
↦∈→⊆⨆dom {⊥} fg () u∈v
↦∈→⊆⨆dom {v ↦ w} fg refl u∈v = u∈v
↦∈→⊆⨆dom {u ⊔ u′} fg (inj₁ v↦w∈u) u∈v =
   let ih = ↦∈→⊆⨆dom (λ z → fg (inj₁ z)) v↦w∈u in
   inj₁ (ih u∈v)
↦∈→⊆⨆dom {u ⊔ u′} fg (inj₂ v↦w∈u′) u∈v =
   let ih = ↦∈→⊆⨆dom (λ z → fg (inj₂ z)) v↦w∈u′ in
   inj₂ (ih u∈v)

⊆↦→⨆cod⊆ : ∀{u v w : Value}
        → u ⊆ v ↦ w
          ---------
        → ⨆cod u ⊆ w
⊆↦→⨆cod⊆ {⊥} s refl with s {⊥} refl
... | ()
⊆↦→⨆cod⊆ {C ↦ C′} s m with s {C ↦ C′} refl
... | refl = m
⊆↦→⨆cod⊆ {u ⊔ u′} s (inj₁ x) = ⊆↦→⨆cod⊆ (λ {C} z → s (inj₁ z)) x
⊆↦→⨆cod⊆ {u ⊔ u′} s (inj₂ y) = ⊆↦→⨆cod⊆ (λ {C} z → s (inj₂ z)) y

factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = all-funs u′  ×  u′ ⊆ u  ×  ⨆dom u′ ⊑ v  ×  w ⊑ ⨆cod u′


sub-inv-trans : ∀{u′ u₂ u : Value}
    → all-funs u′  →  u′ ⊆ u
    → (∀{v′ w′} → v′ ↦ w′ ∈ u → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
      ---------------------------------------------------------------
    → Σ[ u₃ ∈ Value ] factor u₂ u₃ (⨆dom u′) (⨆cod u′)
sub-inv-trans {⊥} {u₂} {u} fu′ u′⊆u IH =
   ⊥-elim (contradiction (fu′ refl) ¬Fun⊥)
sub-inv-trans {u₁′ ↦ u₂′} {u₂} {u} fg u′⊆u IH = IH (↦⊆→∈ u′⊆u)
sub-inv-trans {u₁′ ⊔ u₂′} {u₂} {u} fg u′⊆u IH
    with ⊔⊆-inv u′⊆u
... | ⟨ u₁′⊆u , u₂′⊆u ⟩
    with sub-inv-trans {u₁′} {u₂} {u} (λ {v′} z → fg (inj₁ z)) u₁′⊆u IH
       | sub-inv-trans {u₂′} {u₂} {u} (λ {v′} z → fg (inj₂ z)) u₂′⊆u IH
... | ⟨ u₃₁ , ⟨ fu21' , ⟨ u₃₁⊆u₂ , ⟨ du₃₁⊑du₁′ , cu₁′⊑cu₃₁ ⟩ ⟩ ⟩ ⟩
    | ⟨ u₃₂ , ⟨ fu22' , ⟨ u₃₂⊆u₂ , ⟨ du₃₂⊑du₂′ , cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ (u₃₁ ⊔ u₃₂) , ⟨ fu₂′ , ⟨ u₂′⊆u₂ ,
      ⟨ ⊔⊑⊔ du₃₁⊑du₁′ du₃₂⊑du₂′ ,
        ⊔⊑⊔ cu₁′⊑cu₃₁ cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩
    where fu₂′ : {v′ : Value} → v′ ∈ u₃₁ ⊎ v′ ∈ u₃₂ → Fun v′
          fu₂′ {v′} (inj₁ x) = fu21' x
          fu₂′ {v′} (inj₂ y) = fu22' y
          u₂′⊆u₂ : {C : Value} → C ∈ u₃₁ ⊎ C ∈ u₃₂ → C ∈ u₂
          u₂′⊆u₂ {C} (inj₁ x) = u₃₁⊆u₂ x
          u₂′⊆u₂ {C} (inj₂ y) = u₃₂⊆u₂ y


sub-inv : ∀{u₁ u₂ : Value}
        → u₁ ⊑ u₂
        → ∀{v w} → v ↦ w ∈ u₁
          -------------------------------------
        → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
sub-inv {⊥} {u₂} ⊑-bot {v} {w} ()
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₁ x) = sub-inv lt1 x
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₂ y) = sub-inv lt2 y
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R1 lt) {v} {w} m
    with sub-inv lt m
... | ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ u₃₁⊆u₂₁ , ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ (λ {w} z → inj₁ (u₃₁⊆u₂₁ z)) ,
                                   ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R2 lt) {v} {w} m
    with sub-inv lt m
... | ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ u₃₂⊆u₂₂ , ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ (λ {C} z → inj₂ (u₃₂⊆u₂₂ z)) ,
                                   ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂} (⊑-trans{v = u} u₁⊑u u⊑u₂) {v} {w} v↦w∈u₁
    with sub-inv u₁⊑u v↦w∈u₁
... | ⟨ u′ , ⟨ fu′ , ⟨ u′⊆u , ⟨ domu′⊑v , w⊑codu′ ⟩ ⟩ ⟩ ⟩
    with sub-inv-trans {u′} fu′ u′⊆u (sub-inv u⊑u₂)
... | ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ domu₃⊑domu′ , codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ ⊑-trans domu₃⊑domu′ domu′⊑v ,
                                    ⊑-trans w⊑codu′ codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁₁ ↦ u₁₂} {u₂₁ ↦ u₂₂} (⊑-fun lt1 lt2) refl =
    ⟨ u₂₁ ↦ u₂₂ , ⟨ (λ {w} → fun) , ⟨ (λ {C} z → z) , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
sub-inv {u₂₁ ↦ (u₂₂ ⊔ u₂₃)} {u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃} ⊑-dist
    {.u₂₁} {.(u₂₂ ⊔ u₂₃)} refl =
    ⟨ u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃ , ⟨ f , ⟨ g , ⟨ ⊑-conj-L ⊑-refl ⊑-refl , ⊑-refl ⟩ ⟩ ⟩ ⟩
  where f : all-funs (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃) ⊆ (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y

sub-inv-fun : ∀{v w u₁ : Value}
    → (v ↦ w) ⊑ u₁
      -----------------------------------------------------
    → Σ[ u₂ ∈ Value ] all-funs u₂ × u₂ ⊆ u₁
        × (∀{v′ w′} → (v′ ↦ w′) ∈ u₂ → v′ ⊑ v) × w ⊑ ⨆cod u₂
sub-inv-fun{v}{w}{u₁} abc
    with sub-inv abc {v}{w} refl
... | ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ G , cc ⟩ ⟩ ⟩ ⟩
   where G : ∀{D E} → (D ↦ E) ∈ u₂ → D ⊑ v
         G{D}{E} m = ⊑-trans (⊆→⊑ (↦∈→⊆⨆dom f m)) db

↦⊑↦-inv : ∀{v w v′ w′}
        → v ↦ w ⊑ v′ ↦ w′
          -----------------
        → v′ ⊑ v × w ⊑ w′
↦⊑↦-inv{v}{w}{v′}{w′} lt
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with all-funs∈ f
... | ⟨ u , ⟨ u′ , u↦u′∈Γ ⟩ ⟩
    with Γ⊆v34 u↦u′∈Γ
... | refl =
  let ⨆codΓ⊆w′ = ⊆↦→⨆cod⊆ Γ⊆v34 in
  ⟨ lt1 u↦u′∈Γ , ⊑-trans lt2 (⊆→⊑ ⨆codΓ⊆w′) ⟩