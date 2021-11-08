module 747Inference where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no; does; proof; _because_; ofʸ; ofⁿ)
open import Agda.Builtin.Bool using (true; false)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse; fromWitnessFalse) -- added
import 747DBDefs as DB

-- Syntax.

infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infixr  7  _⇒_

infix   5  ƛ_⇒_
infix   5  μ_⇒_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   8  `suc_
infix   9  `_

Id : Set
Id = String

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                        : Id → Term⁺
  _·_                       : Term⁺ → Term⁻ → Term⁺
  _↓_                       : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  `zero                    : Term⁻
  `suc_                    : Term⁻ → Term⁻
  `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  μ_⇒_                     : Id → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻

-- Examples of terms.

two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ ` "n" ↑
                        |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
            ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

2+2 : Term⁺
2+2 = plus · two · two
Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoᶜ : Term⁻
twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

plusᶜ : Term⁺
plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
             ↓ (Ch ⇒ Ch ⇒ Ch)

sucᶜ : Term⁻
sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

2+2ᶜ : Term⁺
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

-- Lookup judgments.

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  -- The smart constructor, copied from Lambda.

  S : ∀ {Γ x y A B}
    → {x≢y : False (x ≟ y)}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

-- Typing judgments.

data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      -------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x ⦂ `ℕ ⊢ N ↓ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓ B

-- 747/PLFA exercise: NatMul (1 point)
-- Write the term for multiplication of natural numbers,
-- as you did in Lambda, but this time using the definitions above.
{-
mul : Term
mul =  μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ `zero
           |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n") ]

Copy the code of "plus" above and modify it according to "mul" in 747Lambda.
To pass syntax check of "Term⁺" and "Term⁻", we need to use "↑" decorate according items.
-}
mul : Term⁺
mul = (μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ `zero
                        |suc "m" ⇒ plus · (` "n" ↑) · (` "*" · (` "m" ↑) · (` "n" ↑) ↑) ↑  ])
            ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

-- 747/PLFA exercise: ChurchMul (1 point)
-- Same as above, but for multiplication of Church numbers.
{-
Similar idea as above exercise.
-}
mulᶜ : Term⁺
mulᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · ((` "m" · (` "s" ↑)) ↑) · (` "z" ↑) ↑)
             ↓ (Ch ⇒ Ch ⇒ Ch)

-- PLFA exercise: extend the rules to support products (from More)

-- PLFA exercise (stretch): extend the rules to support the other
-- constructs from More.

-- Helper functions for computation of types,
-- mostly needed in "no" decidability cases.

-- Deciding equality of types (needed for the ⊢↑ rule).

_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ      ≟Tp `ℕ              =  yes refl
`ℕ      ≟Tp (A ⇒ B)         =  no λ()
(A ⇒ B) ≟Tp `ℕ              =  no λ()
(A ⇒ B) ≟Tp (A′ ⇒ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _         =  no λ{refl → A≢ refl}
...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
...  | yes refl | yes refl  =  yes refl

-- Domain and range of equal function types are equal,
-- and `ℕ is not a function type.

dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
rng≡ refl = refl

ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
ℕ≢⇒ ()

-- The uniqueness helpers are needed for negative judgments.

-- Lookup judgments are unique.

uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z Z                 =  refl
uniq-∋ Z (S {x≢y = x≢y} _) =  ⊥-elim (toWitnessFalse x≢y refl)
uniq-∋ (S {x≢y = x≢y} _) Z =  ⊥-elim (toWitnessFalse x≢y refl)
uniq-∋ (S ∋x) (S ∋x′)      =  uniq-∋ ∋x ∋x′

-- A synthesized type is unique.

uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl 

-- Failed lookups still fail if a different binding is added.

ext∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ (∃[ A ]( Γ ∋ x ⦂ A ))
    -----------------------------
  → ¬ (∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A ))
ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
ext∋ _   ¬∃ ⟨ A , S ⊢x ⟩  =  ¬∃ ⟨ A , ⊢x ⟩

-- Decision procedure for lookup judgments.

lookup : ∀ (Γ : Context) (x : Id)
    -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅ x                        =  no  (λ ())
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl                    =  yes ⟨ B , Z ⟩
... | no x≢y with lookup Γ x
...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
...             | yes ⟨ A , ⊢x ⟩   =  yes ⟨ A , S {x≢y = fromWitnessFalse x≢y} ⊢x ⟩

-- Helpers for promoting a failure to type.

¬arg : ∀ {Γ A B L M}
  → Γ ⊢ L ↑ A ⇒ B
  → ¬ Γ ⊢ M ↓ A
    -------------------------
  → ¬ (∃[ B′ ](Γ ⊢ L · M ↑ B′))
¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬switch : ∀ {Γ M A B}
  → Γ ⊢ M ↑ A
  → A ≢ B
    ---------------
  → ¬ Γ ⊢ (M ↑) ↓ B
¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B

-- Mutually-recursive synthesize and inherit functions.

synthesize : ∀ (Γ : Context) (M : Term⁺)
    -----------------------
  → Dec (∃[ A ](Γ ⊢ M ↑ A))

inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
    ---------------
  → Dec (Γ ⊢ M ↓ A)

synthesize Γ (` x) with lookup Γ x
... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
synthesize Γ (L · M) with synthesize Γ L
... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) })
... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩  
synthesize Γ (M ↓ A) with inherit Γ M A
... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩

inherit Γ (ƛ x ⇒ N) `ℕ      =  no  (λ())
inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢ƛ ⊢N)
inherit Γ `zero `ℕ          =  yes ⊢zero
inherit Γ `zero (A ⇒ B)     =  no  (λ())
inherit Γ (`suc M) `ℕ with inherit Γ M `ℕ
... | no ¬⊢M                =  no  (λ{ (⊢suc ⊢M)  →  ¬⊢M ⊢M })
... | yes ⊢M                =  yes (⊢suc ⊢M)
inherit Γ (`suc M) (A ⇒ B)  =  no  (λ())
inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with synthesize Γ L
... | no ¬∃                 =  no  (λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩})
... | yes ⟨ _ ⇒ _ , ⊢L ⟩    =  no  (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L) })   
... | yes ⟨ `ℕ ,    ⊢L ⟩ with inherit Γ M A
...    | no ¬⊢M             =  no  (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
...    | yes ⊢M with inherit (Γ , x ⦂ `ℕ) N A
...       | no ¬⊢N          =  no  (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
...       | yes ⊢N          =  yes (⊢case ⊢L ⊢M ⊢N)
inherit Γ (μ x ⇒ N) A with inherit (Γ , x ⦂ A) N A
... | no ¬⊢N                =  no  (λ{ (⊢μ ⊢N) → ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢μ ⊢N)
inherit Γ (M ↑) B with synthesize Γ M
... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)

-- Computed by evaluating 'synthesize ∅ 2+2' (no editing needed!).

⊢2+2 : ∅ ⊢ 2+2 ↑ `ℕ
⊢2+2 =
  ⊢↓
  (⊢μ
   (⊢ƛ
    (⊢ƛ
     (⊢case (⊢` (S Z)) (⊢↑ (⊢` Z) refl)
      (⊢suc
       (⊢↑ (⊢` (S (S (S Z))) · ⊢↑ (⊢` Z) refl · ⊢↑ (⊢` (S Z)) refl)
        refl))))))
  · ⊢suc (⊢suc ⊢zero)
  · ⊢suc (⊢suc ⊢zero)


-- Check that synthesis is correct (more below).

_ : synthesize ∅ 2+2 ≡ yes ⟨ `ℕ , ⊢2+2 ⟩
_ = refl

-- Example: 2+2 for Church numerals.
-- Computed as above.

⊢2+2ᶜ : ∅ ⊢ 2+2ᶜ ↑ `ℕ
⊢2+2ᶜ =
  ⊢↓
  (⊢ƛ
   (⊢ƛ
    (⊢ƛ
     (⊢ƛ
      (⊢↑
       (⊢` (S (S (S Z))) · ⊢↑ (⊢` (S Z)) refl ·
        ⊢↑ (⊢` (S (S Z)) · ⊢↑ (⊢` (S Z)) refl · ⊢↑ (⊢` Z) refl) refl)
       refl)))))
  ·
  ⊢ƛ (⊢ƛ (⊢↑ (⊢` (S Z) · ⊢↑ (⊢` (S Z) · ⊢↑ (⊢` Z) refl) refl) refl))
  ·
  ⊢ƛ (⊢ƛ (⊢↑ (⊢` (S Z) · ⊢↑ (⊢` (S Z) · ⊢↑ (⊢` Z) refl) refl) refl))
  · ⊢ƛ (⊢suc (⊢↑ (⊢` Z) refl))
  · ⊢zero

_ : synthesize ∅ 2+2ᶜ ≡ yes ⟨ `ℕ , ⊢2+2ᶜ ⟩
_ = refl

-- Testing error cases (important!).

_ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ (`ℕ ⇒ `ℕ)) ≡ no _
_ = refl

-- Bad argument type.

_ : synthesize ∅ (plus · sucᶜ) ≡ no _
_ = refl

-- Bad function types.

_ : synthesize ∅ (plus · sucᶜ · two) ≡ no _
_ = refl

_ : synthesize ∅ ((two ↓ `ℕ) · two) ≡ no _
_ = refl

_ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡ no _
_ = refl

-- A natural can't have a function type.

_ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl

_ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl

-- Can't hide a bad type.

_ : synthesize ∅ (`suc twoᶜ ↓ `ℕ) ≡ no _
_ = refl

-- Can't case on a function type.

_ : synthesize ∅
      ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl

-- Can't hide a bad type inside case.

_ : synthesize ∅
      ((`case (twoᶜ ↓ `ℕ) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl

-- Mismatch of inherited and synthesized types.

_ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡ no _
_ = refl


-- Erasure: Taking the evidence provided by synthesis on a decorated term
-- and producing the corresponding inherently-typed term.

-- Erasing a type.

∥_∥Tp : Type → DB.Type
∥ `ℕ ∥Tp             =  DB.`ℕ
∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp

-- Erasing a context.

∥_∥Cx : Context → DB.Context
∥ ∅ ∥Cx              =  DB.∅
∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp

-- Erasing a lookup judgment.

∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
∥ Z ∥∋               =  DB.Z
∥ S ⊢x ∥∋         =  DB.S ∥ ⊢x ∥∋

-- Mutually-recursive functions to erase typing judgments.

∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻

∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
∥ ⊢zero ∥⁻           =  DB.`zero
∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺

-- Tests that erasure works.
-- (It produces the terms we defined in DeBruijn.)

_ : ∥ ⊢2+2 ∥⁺ ≡ DB.2+2
_ = refl

_ : ∥ ⊢2+2ᶜ ∥⁺ ≡ DB.2+2ᶜ
_ = refl

-- PLFA exercise: demonstrate that synthesis on your decorated multiplication
-- (both for naturals and Church numbers)
-- followed by erasure gives your inherently-typed multiplication
-- (from DeBruijn).
-- Although there are no marks for this, this is a useful check
-- on your understanding, and you should consider doing it.

-- PLFA exercise: extend the above to include products.

-- PLFA exercise (stretch): extend the above to include
-- the rest of the features added in More.

-- 747 extended exercise: bidirectional typing on plain terms.
-- The synthesis/inheritance decorations (particularly ↑) are annoying,
-- and seem like they could be automated.
-- The main issue is that not all plain terms can be decorated,
-- and we have to avoid partial functions.
-- The proof by reflection idea can be used to our advantage.

-- Here are the constructors for plain terms copied
-- from Lambda, with type annotation added (last constructor).

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  `case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term
  _⦂_                     :  Term → Type → Term

-- Data definitions of synthesizable and inheritable.

data Synth : Term → Set
data Inherit : Term → Set

data Synth where
  var : {x : Id} → Synth (` x)
  app : {M N : Term} → Synth M →  Inherit N → Synth (M · N)
  ann : {M : Term} → {T : Type} → Inherit M → Synth (M ⦂ T)

data Inherit where
  lam : {x : Id} → {M : Term} → Inherit M → Inherit (ƛ x ⇒ M)
  zer : Inherit `zero
  suc : {M : Term} → Inherit M → Inherit (`suc M)
  case : {M : Term} → {Z : Term} → {n : Id} → {S : Term}
    → Synth M → Inherit Z → Inherit S
    → Inherit (`case M [zero⇒ Z |suc n ⇒ S ])
  mu : {x : Id} → {M : Term} → Inherit M → Inherit (μ x ⇒ M)
  up : {M : Term} → Synth M → Inherit M

-- 747 exercise: DecideBidirect (5 points)
-- Implement the decision functions for Synth and Inherit.
{-
Basically we use with clause according to the signature of definition (constructor).
Then a few cases can be solved directly by C-c C-a.
For the remaining cases, after with clause, the all true cases can be solved directly by C-c C-a and
for the other cases in the with clause we should use pattern matching of lambda to get evidence of ¬.
Use "up" when no direct constructor available.
Then all cases can be solved by C-c C-a.
-}
isSynth : (t : Term) → Dec (Synth t)
isInherit : (t : Term) → Dec (Inherit t)

isSynth (` x) = yes var
isSynth (ƛ x ⇒ t) = no (λ ())
isSynth (t · t₁) 
  with (isSynth t) |  (isInherit t₁)
... | .true because ofʸ p | .true because ofʸ p₁ = yes (app p p₁)
... | .true because ofʸ p | .false because ofⁿ ¬p = false because (ofⁿ (λ { (app a b) → ¬p b}))
... | .false because ofⁿ ¬p | .true because ofʸ p = false because (ofⁿ (λ { (app a b) → ¬p a}))
... | .false because ofⁿ ¬p | .false because ofⁿ ¬p₁ = false because (ofⁿ (λ { (app a b) → ¬p₁ b}))
isSynth `zero = no (λ ())
isSynth (`suc t) = no (λ ())
isSynth `case t [zero⇒ t₁ |suc x ⇒ t₂ ] = no (λ ())
isSynth (μ x ⇒ t) = no (λ ())
isSynth (t ⦂ x) with isInherit t
... | .true because ofʸ p = yes (ann p)
... | .false because ofⁿ ¬p = false because (ofⁿ (λ {(ann a) → ¬p a }))

isInherit (` x) = yes (up var)
isInherit (ƛ x ⇒ t) with isInherit t 
... | true because ofʸ p = yes (lam p)
... | false because ofⁿ ¬p = false because ofⁿ (λ {(lam a) → ¬p a })
isInherit (t · t₁) with (isSynth t) |  (isInherit t₁)
... | .true because ofʸ p | .true because ofʸ p₁ = yes (up (app p p₁))
... | .true because ofʸ p | .false because ofⁿ ¬p = false because ofⁿ (λ {(up (app a b)) →  ¬p b})
... | .false because ofⁿ ¬p | .true because ofʸ p = false because ofⁿ (λ {(up (app a b)) →  ¬p a})
... | .false because ofⁿ ¬p | .false because ofⁿ ¬p₁ = false because ofⁿ (λ {(up (app a b)) →  ¬p₁ b})
isInherit `zero = yes zer
isInherit (`suc t) with isInherit t 
... | true because ofʸ p = yes (suc p)
... | false because ofⁿ ¬p = false because ofⁿ (λ {(suc a) → ¬p a })
isInherit `case t [zero⇒ t₁ |suc x ⇒ t₂ ] with isSynth t | isInherit t₁ | isInherit t₂ 
... | .true because ofʸ p | .true because ofʸ p₁ | .true because ofʸ p₂ = yes (case p p₁ p₂)
... | .true because ofʸ p | .true because ofʸ p₁ | .false because ofⁿ ¬p = false because (ofⁿ (λ {(case a b c) → ¬p c}))
... | .true because ofʸ p | .false because ofⁿ ¬p | .true because ofʸ p₁ = false because (ofⁿ (λ {(case a b c) → ¬p b}))
... | .true because ofʸ p | .false because ofⁿ ¬p | .false because ofⁿ ¬p₁ = false because (ofⁿ (λ {(case a b c) → ¬p₁ c}))
... | .false because ofⁿ ¬p | .true because ofʸ p | .true because ofʸ p₁ = false because (ofⁿ (λ {(case a b c) → ¬p a}))
... | .false because ofⁿ ¬p | .true because ofʸ p | .false because ofⁿ ¬p₁ = false because (ofⁿ (λ{(case a b c) → ¬p₁ c}))
... | .false because ofⁿ ¬p | .false because ofⁿ ¬p₁ | .true because ofʸ p = false because (ofⁿ (λ {(case a b c) → ¬p₁ b}))
... | .false because ofⁿ ¬p | .false because ofⁿ ¬p₁ | .false because ofⁿ ¬p₂ = false because (ofⁿ (λ {(case a b c) → ¬p₂ c}))
isInherit (μ x ⇒ t) with isInherit t 
... | true because ofʸ p = yes (mu p)
... | false because ofⁿ ¬p = false because (ofⁿ (λ {(mu a) → ¬p a }))
isInherit (t ⦂ x) with isInherit t
... | true because ofʸ p = yes (up (ann p))
... | false because ofⁿ ¬p = false because (ofⁿ (λ {(up (ann a)) →  ¬p a}))

-- 747 exercise: Decorate (3 points)
-- Implement the mutually-recursive decorators.
{-
We need to ensure exactly one-to-one mapping.
We write code by frequently checking signature of definitions.
C-c C-a will give obvious wrong answer in this exercise.
Use Class name and operator "." to resolve ambiguity.
There is no way to convert "Inherit M" to "Synth M", so some cases in "decorate⁺" is absurdity.

Basically it is manipulating building blocks under constraints of definitions to make a perfect mapping 
and we definitly need some tests to prove the correctness of this exercise.
We should only case split once since the case split will not end for some cases and 
the solution is using recursion to avoid infinite split.
-}
decorate⁻ : (t : Term) → Inherit t → Term⁻
decorate⁺ : (t : Term) → Synth t → Term⁺

decorate⁻ (` x) = λ _ → ` x ↑
decorate⁻ (ƛ x ⇒ t) = λ {(lam it) → Term⁻.ƛ_⇒_ x (decorate⁻ t it)} 
decorate⁻ (t · t₁) = λ { (up (app st it₁)) → (Term⁺._·_ (decorate⁺ t st) (decorate⁻ t₁ it₁)) ↑  }
decorate⁻ `zero = λ _ → Term⁻.`zero
decorate⁻ (`suc t) = λ {(suc it) → Term⁻.`suc (decorate⁻ t it) }
decorate⁻ `case t [zero⇒ t₁ |suc x ⇒ t₂ ] = λ {(case st it₁ it₂) → 
  Term⁻.`case_[zero⇒_|suc_⇒_] (decorate⁺ t st) (decorate⁻ t₁ it₁) x (decorate⁻ t₂ it₂) }
decorate⁻ (μ x ⇒ t) = λ {(mu it) → Term⁻.μ_⇒_ x (decorate⁻ t it)}
decorate⁻ (t ⦂ x) = λ {(up (ann it)) →  ((decorate⁻ t it) ↓ x) ↑}

decorate⁺ (` x) = λ _ → ` x
decorate⁺ (ƛ x ⇒ t) = λ ()
decorate⁺ (t · t₁) = λ {(app st it₁) → Term⁺._·_ (decorate⁺ t st) (decorate⁻ t₁ it₁) } 
decorate⁺ `zero = λ ()
decorate⁺ (`suc t) = λ ()
decorate⁺ `case t [zero⇒ t₁ |suc x ⇒ t₂ ] = λ ()
decorate⁺ (μ x ⇒ t) = λ ()
decorate⁺ (t ⦂ x) = λ {(ann it) →  ((decorate⁻ t it) ↓ x)}

-- 747 exercise: ToTerm (2 points)
-- Use the proof by reflection idea as before to
-- automatically compute the supporting proofs for literal terms
-- and hide them away.
{-
Use "toWitness" to get evidence, which is the second argument of decorate functions. 
-}
toTerm⁺ : (t : Term) → {i : True (isSynth t)} → Term⁺
toTerm⁺ t {i} = decorate⁺ t (toWitness i)

toTerm⁻ : (t : Term) → {i : True (isInherit t)} → Term⁻
toTerm⁻ t {i} = decorate⁻ t (toWitness i)

-- Examples from Lambda which serve as unit tests for the above.

ltwo : Term
ltwo = `suc `suc `zero

lplus : Term
lplus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case ` "m"
            [zero⇒ ` "n"
            |suc "m" ⇒ `suc (` "p" · ` "m" · ` "n") ])
         ⦂ (`ℕ ⇒ `ℕ ⇒ `ℕ)

l2+2 : Term
l2+2 = lplus · ltwo · ltwo

ltwoᶜ : Term
ltwoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

lplusᶜ : Term
lplusᶜ =  (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
         ⦂ (Ch ⇒ Ch ⇒ Ch)

lsucᶜ : Term
lsucᶜ = ƛ "x" ⇒ `suc (` "x")

l2+2ᶜ : Term
l2+2ᶜ = lplusᶜ · ltwoᶜ · ltwoᶜ · lsucᶜ · `zero



_ : toTerm⁻ ltwo ≡ two
_ = refl

_ : toTerm⁺ lplus ≡ plus
_ = refl

_ : toTerm⁺ l2+2 ≡ 2+2
_ = refl

_ : toTerm⁻ ltwoᶜ ≡ twoᶜ
_ = refl

_ : toTerm⁺ lplusᶜ ≡ plusᶜ
_ = refl

_ : toTerm⁻ lsucᶜ ≡ sucᶜ
_ = refl

_ : toTerm⁺ l2+2ᶜ ≡ 2+2ᶜ
_ = refl



-- 747 exercise: ontoTerm (3 points)
-- Show that Synth and Inherit definitions are inclusive enough,
-- that is, for every Term⁻ there is a plain term with inherit evidence
-- that maps onto it, and similarly for Term⁺. Why is it not an isomorphism?

Term⁻-to-Term : ∀ (t⁻ : Term⁻) → Term
Term⁺-to-Term : ∀ (t⁺ : Term⁺) → Term

Term⁻-to-Term (ƛ x ⇒ t⁻) = Term.ƛ_⇒_ x (Term⁻-to-Term t⁻)
Term⁻-to-Term `zero = Term.`zero
Term⁻-to-Term (`suc t⁻) = Term.`suc (Term⁻-to-Term t⁻)
Term⁻-to-Term `case x [zero⇒ t⁻ |suc x₁ ⇒ t⁻₁ ] = Term.`case_[zero⇒_|suc_⇒_] (Term⁺-to-Term x) (Term⁻-to-Term t⁻) x₁ (Term⁻-to-Term t⁻₁)
Term⁻-to-Term (μ x ⇒ t⁻) = Term.μ_⇒_ x (Term⁻-to-Term t⁻)
Term⁻-to-Term (x ↑) = (Term⁺-to-Term x)

Term⁺-to-Term (` x) = Term.`_ x
Term⁺-to-Term (t⁺ · x) = Term._·_ (Term⁺-to-Term t⁺) (Term⁻-to-Term x)
Term⁺-to-Term (x ↓ x₁) = Term._⦂_ (Term⁻-to-Term x) x₁


Term⁻-to-Inherit : ∀ (t⁻ : Term⁻) → Inherit (Term⁻-to-Term t⁻)
Term⁺-to-Synth : ∀ (t⁺ : Term⁺) → Synth (Term⁺-to-Term t⁺)

Term⁻-to-Inherit (ƛ x ⇒ t⁻) = lam (Term⁻-to-Inherit t⁻)
Term⁻-to-Inherit `zero = zer
Term⁻-to-Inherit (`suc t⁻) = suc (Term⁻-to-Inherit t⁻)
Term⁻-to-Inherit `case x [zero⇒ t⁻ |suc x₁ ⇒ t⁻₁ ] = Inherit.case (Term⁺-to-Synth x) (Term⁻-to-Inherit t⁻)  (Term⁻-to-Inherit t⁻₁)
Term⁻-to-Inherit (μ x ⇒ t⁻) = mu (Term⁻-to-Inherit t⁻)
Term⁻-to-Inherit (x ↑) = up (Term⁺-to-Synth x)

Term⁺-to-Synth (` x) = var
Term⁺-to-Synth (t⁺ · x) = Synth.app (Term⁺-to-Synth t⁺) (Term⁻-to-Inherit x)
Term⁺-to-Synth (x ↓ x₁) = Synth.ann (Term⁻-to-Inherit x)


decorate⁻-to-from : ∀ (t⁻ : Term⁻) → decorate⁻ (Term⁻-to-Term t⁻) (Term⁻-to-Inherit t⁻) ≡ t⁻
decorate⁺-to-from : ∀ (t⁺ : Term⁺) → decorate⁺ (Term⁺-to-Term t⁺) (Term⁺-to-Synth t⁺) ≡ t⁺

helper : ∀ (t⁺ : Term⁺) →  decorate⁻ (Term⁺-to-Term t⁺) (up (Term⁺-to-Synth t⁺)) ≡ (decorate⁺ (Term⁺-to-Term t⁺) (Term⁺-to-Synth t⁺)) ↑
helper (` x) = refl
helper (t⁺ · x) = refl
helper (x ↓ x₁) = refl

decorate⁻-to-from (ƛ x ⇒ t⁻) rewrite decorate⁻-to-from t⁻ = refl
decorate⁻-to-from `zero = refl
decorate⁻-to-from (`suc t⁻) rewrite decorate⁻-to-from t⁻ = refl
decorate⁻-to-from `case x [zero⇒ t⁻ |suc x₁ ⇒ t⁻₁ ] 
  rewrite decorate⁺-to-from x | decorate⁻-to-from t⁻ | decorate⁻-to-from t⁻₁ = refl
decorate⁻-to-from (μ x ⇒ t⁻) rewrite decorate⁻-to-from t⁻ = refl
decorate⁻-to-from (x ↑) rewrite (helper x) | decorate⁺-to-from x = refl


decorate⁺-to-from (` x) = refl
decorate⁺-to-from (t⁺ · x) rewrite decorate⁻-to-from x | decorate⁺-to-from t⁺ = refl
decorate⁺-to-from (x ↓ x₁) rewrite decorate⁻-to-from x = refl


ontoTerm⁻ : ∀ (t⁻ : Term⁻) → ∃[ t ] (∃[ i ] (decorate⁻ t i ≡ t⁻))
ontoTerm⁺ : ∀ (t⁺ : Term⁺) → ∃[ t ] (∃[ s ] (decorate⁺ t s ≡ t⁺))

ontoTerm⁻ t⁻ = ⟨ (Term⁻-to-Term t⁻) , ⟨ Term⁻-to-Inherit t⁻ , decorate⁻-to-from t⁻ ⟩ ⟩

ontoTerm⁺ t⁺ =   ⟨ (Term⁺-to-Term t⁺) , ⟨ Term⁺-to-Synth t⁺ , decorate⁺-to-from t⁺ ⟩ ⟩

{- 
  Unicode used in this chapter:

  ↓  U+2193:  DOWNWARDS ARROW (\d)
  ↑  U+2191:  UPWARDS ARROW (\u)
  ∥  U+2225:  PARALLEL TO (\||)

-}  