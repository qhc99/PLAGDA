module 747Properties where

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
open import 747LambdaDefs

-- There are too many definitions to copy over, so please
-- make sure that a copy of 747LambdaDefs.agda (from "starter")
-- is in the same directory as this file.

-- Values do not step.

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-suc vm) (ξ-suc msn) = V¬—→ vm msn

-- Step implies "not a value".

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V msn vm = V¬—→ vm msn

-- Evidence of canonical forms for well-typed values.

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

-- Every closed, well-typed value is canonical.
-- (That is, we got all the cases in the above definition.)

canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A

-- canonical v:a vv
canonical (⊢ƛ v:a) V-ƛ = C-ƛ v:a
canonical ⊢zero V-zero = C-zero
canonical (⊢suc v:a) (V-suc vv) = C-suc (canonical v:a vv)

-- If a term is canonical, it is a value.

value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value (C-ƛ x) = V-ƛ
value C-zero = V-zero
value (C-suc cm:a) = V-suc (value cm:a)

-- If a term is canonical, it is well-typed in the empty context.

typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ x) = ⊢ƛ x
typed C-zero = ⊢zero
typed (C-suc cm:a) = ⊢suc (typed cm:a)

-- Evidence for the progress theorem.
-- Either a step can be taken, or we're done (at a value).

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

-- The progress theorem: a term well-typed in the empty context satisfies Progress.

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

-- 747/PLFA exercise: AltProg (5 points)
-- Here is an alternate formulation of progress.
-- Show that it is isomorphic to Progress M, and prove this form
-- of the progress theorem directly.

progress-iso : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
progress-iso {M} = mk-≃ progress-iso-to progress-iso-from progress-iso-from∘to progress-iso-to∘form
  where
  {-
  Case split.
  For function "step", we need to specify its implicit argument since it is very very very useful...
  Basically we need to decide which inj to use by the idea of "V¬—→" and "—→¬V" above.
  -}
  progress-iso-to :  ∀ {P} → Progress P → Value P ⊎ ∃-syntax (_—→_ P)
  progress-iso-to (step {n} x) = inj₂ ⟨ n , x ⟩
  progress-iso-to (done x) = inj₁ x

  {-
  Case split "_⊎_".
  In the first case we have "Value M", so we should refine on "done".
  In the second case, since we do not have "Value M", the only remain option is "step".
  -}
  progress-iso-from : Value M ⊎ ∃-syntax (_—→_ M) → Progress M
  progress-iso-from (inj₁ x) = done x
  progress-iso-from (inj₂ ⟨ fst , snd ⟩) = step snd

 {-compute on goal get refl.-}
  progress-iso-from∘to : (x : Progress M) → progress-iso-from (progress-iso-to x) ≡ x
  progress-iso-from∘to (step x) = refl
  progress-iso-from∘to (done x) = refl

  {-for the second case, refine get refl.-}
  progress-iso-to∘form : (y : Value M ⊎ ∃-syntax (_—→_ M)) → progress-iso-to (progress-iso-from y) ≡ y
  progress-iso-to∘form (inj₁ x) = refl
  progress-iso-to∘form (inj₂ y) = refl

{-Since we know "Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)"-}
progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ M x = (_≃_.to progress-iso) (progress x)

-- 747/PLFA exercise: ValueEh (1 point)
-- Write a function to decide whether a well-typed term is a value.
-- Hint: reuse theorems proved above to do most of the work.

{-we know there is a progress, so we use with clause there. Then it becomes easy to prove.-}
value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? x with progress x 
... | step x₁ = no (—→¬V  x₁)
... | done x₁ = yes x₁

-- Preservation: types are preserved by reduction.

-- Extension lemma: helper for the renaming lemma that follows.

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z = Z
ext ρ (S x lj) = S x (ρ lj)

-- Renaming lemma: if context Δ extends Γ,
-- then type judgments using Γ can be done using Δ.

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

-- Above is a general lemma which we need in three specific cases.

-- Weaken: a type judgment in the empty context can be weaked to any context.
-- (Can use C-c C-h to ease write the helper function ρ.)

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

-- Drop: a type judgment in a context with a repeated variable
-- can drop the earlier occurrence.

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

-- Swap: if the two most recent additions to the context are for
-- different variables, they can be swapped.

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

-- Substitution lemma: substitution preserves types.

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

-- PLFA exercise: if you did the refactoring of substitution in Lambda,
-- redo subst to work with that definition.

-- Finally, a step of a well-typed term preserves types.

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


-- Evaluation.
-- We get this easily by iterating progress and preservation.

-- Problem: some computations do not terminate.
-- Agda will not let us write a partial function.

sucμ  =  μ "x" ⇒ `suc (` "x")

_ =
  begin
    sucμ
  —→⟨ β-μ ⟩
    `suc sucμ
  —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ
  --  ...
  ∎

-- One solution: supply "gas" (an integer limiting number of steps)

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


eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L

-- We can now write the evaluator.

eval {L} (gas zero)    ⊢L                                =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin


-- A typing judgment for our previous example.

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

-- Running the nonterminating example for three steps.
-- Use C-c C-n, paste in LHS, copy RHS out of result

_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"
   —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
   ∎)
   out-of-gas
_ = refl

-- PLFA exercise: use the evaluator to confirm that two times two is four.
-- PLFA exercise (recommended):
{-
-- need to delete "open import" of 747LambdaDefs and import below
open import 747Lambdas
open import 747Connectives
⊢2*2 : ∅ ⊢ mul · two · two ⦂ `ℕ
⊢2*2 = ⊢mul · ⊢two · ⊢two

-}

-- Without peeking, write down the statements of progress and preservation.
-- PLFA exercise: subject expansion

-- Well-typed terms don't get stuck.

-- A term is normal (or a normal form) if it cannot reduce.

Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)

-- A stuck term is normal, but not a value.

Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M

-- 747/PLFA exercise: Unstuck (3 points)
-- Using progress and preservation, prove the following:
{-
The two constructors of "Progress" make one component of "Stuck" produce the evidence of "⊥".
We use "with" and "progress m:a " to get "Progress" and to case split.
-}
unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck m:a ⟨ n , ¬v ⟩ with progress m:a 
... | step x = n x
... | done x = ¬v x

{-
Induction on the "M —↠ N", every recursion reduce one step "_—→_".
By "preserve m:a x" we get evidence of "M₁ —↠ N", which is second argument of recursion.
-}
preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves m:a (_ ∎) = m:a
preserves m:a (_ —→⟨ x ⟩ msn) = preserves (preserve m:a x) msn

{-
To get "¬ (Stuck N)" from "unstuck", we need "∅ ⊢ N ⦂ A", which can be built by "preserves".
Then we got the answer.
-}
wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs m:a msn = unstuck (preserves m:a msn)

-- PLFA exercise: give an ill-typed term that does get stuck.
-- Reduction is deterministic, proved.

{-
irony function name...

stuck : ∀ {∅ M A}
  → ¬ (∅ ⊢ M ⦂ A)
  → (Stuck M)
proj₁ (stuck {c} {m} {a} x) x₁ = {!   !}
proj₂ (stuck {c} {m} {a} x) x₁ = {!   !}
-}

-- Helper lemma (not needed if 'rewrite' used).

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

-- PLFA's proof of deterministic reduction.
-- (Can be simplified using 'rewrite', but not much.)

det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″

det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  ⊥-elim (V¬—→ V-ƛ L—→L′)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ V-ƛ L—→L″)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  ⊥-elim (V¬—→ V-zero L—→L′)
det (ξ-case L—→L′) (β-suc VL)       =  ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero         (ξ-case M—→M″)   =  ⊥-elim (V¬—→ V-zero M—→M″)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl