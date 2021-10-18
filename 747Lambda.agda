module 747Lambda where

-- Library

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Bool using (T; not)
open import Data.String using (String; _≟_) 
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Function using (_∘_)

-- copied from 747Isomorphism

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

-- Identifiers are strings (for familiarity; later, a better choice).

Id : Set
Id = String

-- Precedence and associativity for our language syntax.

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

-- Syntax of terms.

data Term : Set where
  `_                      :  Id → Term            -- variable
  ƛ_⇒_                    :  Id → Term → Term     -- lambda (abstraction)
  _·_                     :  Term → Term → Term   -- application
  `zero                   :  Term     
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term     -- fixpoint for recursion

-- Example expressions.

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ] 

2+2 : Term
2+2 = plus · two · two

-- Examples using Church numerals.
-- These take "interpretations" of suc and zero
-- and can be used as functions without resorting to case.

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

-- plusᶜ can be defined without using fixpoint.

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

fourᶜ : Term
fourᶜ = plusᶜ · twoᶜ · twoᶜ

-- 747/PLFA exercise: NatMul (1 point)
-- Write multiplication for natural numbers.
-- Alas, refinement will not help, and there is no way (yet) to write tests.
{-
By the example of "plus", we know that it is another language to describe the same thing.
So we just need to express the "_*_" for "ℕ" in this new language.
And definition of "_*_" is:
"
_*_ : ℕ → ℕ → ℕ
zero * n =  zero  
suc m * n =  n + m * n  
"
-}
mul : Term
mul =  μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ `zero
           |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n") ]

-- 747/PLFA exercise: ChurchMul (1 point)
-- Write multiplication for Church numbers.
-- Use of plusᶜ is optional! fixpoint is not needed.
{-
" ƛ "n" ⇒ ƛ "s" " is a function which make n times suc on the input.

threeᶜ : Term
threeᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" ∙ (` "s" · (` "s" · ` "z"))

Let us verify the function by hand unrolling:
sixᶜ ≡ mulᶜ ∙ twoᶜ ∙ threeᶜ ∙ sucᶜ ∙ `zero
    ≡⟨ simply replace ⟩ 
      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ∙ 
      ((ƛ "s" ⇒ ƛ "z" ⇒ ` "s" ∙ (` "s" · (` "s" · ` "z"))) ∙ (ƛ "n" ⇒ `suc (` "n"))) ∙ 
      `zero
    ≡⟨ unroll the second line (or the second item) ⟩ 
      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ∙ 
      ((ƛ "n" ⇒ `suc (` "n")) ∙ ((ƛ "n" ⇒ `suc (` "n")) · ((ƛ "n" ⇒ `suc (` "n")) · ` "z")))) ∙ 
      `zero
    ≡⟨ apply first function to the second and thrid line (or item) ⟩ 
      ((ƛ "n" ⇒ `suc (` "n")) ∙ ((ƛ "n" ⇒ `suc (` "n")) · ((ƛ "n" ⇒ `suc (` "n")) · ` "z")))) ∙ 
      (((ƛ "n" ⇒ `suc (` "n")) ∙ ((ƛ "n" ⇒ `suc (` "n")) · ((ƛ "n" ⇒ `suc (` "n")) · ` "z"))))) ∙ zero
    ≡ 
      `suc `suc `suc `suc `suc `suc `zero
-}

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · (` "n" · ` "s") · ` "z"

-- These definitions let us avoid some backticks and quotes.

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

-- An example of the use of the new notation.

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

-- PLFA exercise: use the new notation to define multiplication.
  
-- Bound variables, free variables, closed terms, open terms, alpha renaming.

-- Values.

data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

-- Substitution is important in defining reduction. 
-- Defined here only for closed terms (simpler).

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]


-- Some examples of substitution.

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡  sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡  ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- quiz
_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

-- PLFA exercise: eliminate common code in above with a helper function.

-- Single-step reduction (written \em\to).
-- Compatibility rules (descending into subexpressions) written with \xi (ξ).
-- "Computation here" rules written with \beta (β).

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

{-
Quiz
1.What does the following term step to? answer: 1

(ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???
1.(ƛ "x" ⇒ ` "x")
2.(ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
3.(ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")


2).What does the following term step to? answer: 1

(ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???
1.(ƛ "x" ⇒ ` "x")
2.(ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
3.(ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")


3).What does the following term step to? (Where twoᶜ and sucᶜ are as defined above.) answer: 1

twoᶜ · sucᶜ · `zero  —→  ???
1.sucᶜ · (sucᶜ · `zero)
2.(ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
3.`zero


-}

-- Arguments reduced to values before beta-reduction (call-by-value).
-- Terms reduced from left to right.
-- Reduction is deterministic (no choice!).
-- You should be able to prove this now, but it's done later, in Properties.

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

-- Multistep: the reflexive-transitive closure of single-step.
-- (Notation below resembles tabular reasoning for equivalence,
--  but note we are not using transitivity.)
-- Written \em\rr-.

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- An alternate definition which makes "reflexive-transitive closure" more obvious.

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

-- 747/PLFA exercise: StepEmbedsIntoStepPrime (2 points)
-- Show that the first definition embeds into the second.
-- Why is it not an isomorphism?
{-
Refine and where pattern.
-}
ms1≤ms2 : ∀ {M N} → (M —↠ N) ≲ (M —↠′ N)
ms1≤ms2 {M} {N} = record { to = ms1≤ms2-to ; from = ms1≤ms2-from ; from∘to = ms1≤ms2-from∘to }
  where
  {-
  Case split. 
  The first case can be built directly by "refl′"
  The second case need the "trans′" rule. 
  We have goal "P —↠′ Q" and context "x : P —→ M₁" "x₁ : M₁ —↠ Q".
  By applying "step′" and induction respectively to "x" and "x₁", we transform the "—→" and "—↠" to "—↠'". 
  Then by "trans′" we got the answer
  -}
  ms1≤ms2-to : ∀ {P Q} →  P —↠ Q → P —↠′ Q
  ms1≤ms2-to {P} {_} (_ ∎) = refl′
  ms1≤ms2-to (_ —→⟨ x ⟩ x₁) = trans′ (step′ x) (ms1≤ms2-to x₁)

  {-
  Case split.
  For the first case, we have "P —→ Q" and the goal is "P —↠ Q".
  There is no "step" for "—→", so we need the helper "Q —→ Q", which is "Q ∎".

  The second case is quite straightforward.

  For the thrid case, double case split dose not work!!!
  We just case split on the first variable and in the second case we have a middle term that is not in the scope.
  So we case split on the first variable again to get the hidden item. 
  Then we will find that we now have another form of induction.
  We tried the new induction form and find there is no longer the "termination checking failed".
  Basically we have got a reduction on the first input variable.
  -}
  ms1≤ms2-from : ∀ {P Q} →  P —↠′ Q → P —↠ Q
  ms1≤ms2-from {P} {Q} (step′ x) = P —→⟨ x ⟩ Q ∎
  ms1≤ms2-from {P} {_} refl′ = P ∎
  ms1≤ms2-from {P} {Q} (trans′ x x₁) = trans (ms1≤ms2-from x) (ms1≤ms2-from x₁)
    where        
    trans : ∀ {L M1 N1}
      → L —↠ M1
      → M1 —↠ N1
      -------
      → L —↠ N1
    trans (_ ∎) mn = mn
    trans (l —→⟨ x ⟩ _ ∎) mn = l —→⟨ x ⟩ mn
    trans (l —→⟨ x ⟩ m2 —→⟨ x₁ ⟩ lm) mn = l —→⟨ x ⟩ (m2 —→⟨ x₁ ⟩ (trans lm mn ) )

  {-
  Case split.
  For the first case, compute the goal using command C-c C-n got refl.

  For the second case, compute the goal, we got "(t —→⟨ x ⟩ ms1≤ms2-from (ms1≤ms2-to x₁)) ≡ (t —→⟨ x ⟩ x₁)".
  By induction we have "ms1≤ms2-from (ms1≤ms2-to x₁) ≡ x₁", then we got the answer.
  -}
  ms1≤ms2-from∘to : ∀ {P Q} →  (x : P —↠ Q) → (ms1≤ms2-from ∘ ms1≤ms2-to) x ≡ x
  ms1≤ms2-from∘to (_ ∎) = refl
  ms1≤ms2-from∘to (t —→⟨ x ⟩ x₁) rewrite ms1≤ms2-from∘to x₁ = refl


-- Determinism means we avoid having to worry about confluence.

-- An example of a multistep reduction.
-- (Not generated by hand, as we'll see later.)
-- Agda can fill in the justifications but not the intermediate terms. Why not?
-- We'll see how to get Agda to do that in 747Properties (it's really cool).

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎

-- Two plus two is four.

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎

-- A longer example of a multistep reduction.

_ : fourᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

-- PLFA exercise: write out the reduction sequence showing one plus one is two.

-- Adding types to our language.

-- Syntax of types.

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

{-
Quiz

What is the type of the following term?

ƛ "s" ⇒ ` "s" · (` "s"  · `zero)

1.(`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ)
2.(`ℕ ⇒ `ℕ) ⇒ `ℕ
3.`ℕ ⇒ (`ℕ ⇒ `ℕ)
4.`ℕ ⇒ `ℕ ⇒ `ℕ
5.`ℕ ⇒ `ℕ
6.`ℕ
Give more than one answer if appropriate.
Answer: 5

What is the type of the following term?

(ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ

1.(`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ)
2.(`ℕ ⇒ `ℕ) ⇒ `ℕ
3.`ℕ ⇒ (`ℕ ⇒ `ℕ)
4.`ℕ ⇒ `ℕ ⇒ `ℕ
5.`ℕ ⇒ `ℕ
6.`ℕ
Give more than one answer if appropriate.
Answer: 6
-}

-- Contexts provide types for free variables.
-- Essentially a list of (name, type) pairs, most recently added to right.

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

-- The lookup judgment.
-- The constructor names are meant to be evocative
-- but for now think of them as 'here' and 'there'.
-- Important: if a parameter name is reused, the latest one is in scope.

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A
    
-- Providing the string inequality proofs required by S
-- can be annoying, and computed proofs can be lengthy.
-- We use the proof by reflection technique described in chapter Decidable
-- to write a "smart" version of S.

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-- The typing judgment.
-- Intro/elim names in comments.

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
       -------------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

-- A convenient way of asserting inequality.
-- (Avoids issues with normalizing evidence of negation.)

_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥

-- A typing derivation for the Church numeral twoᶜ.
-- Most of this can be done with refining (why not all?).

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ ((⊢` (S′ Z)) · ((⊢` (S′ Z)) · (⊢` Z))))

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

-- A typing derivation for "two plus two".
-- Done in arbitrary contexts to permit reuse.

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S′ Z)) (⊢` Z) (⊢suc (((⊢` (S′ (S′ (S′ Z)))) · (⊢` Z)) · (⊢` (S′ Z)))))))

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = (⊢plus · ⊢two) · ⊢two

⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (((⊢` (S′ (S′ (S′ Z)))) · ⊢` (S′ Z)) · (((⊢` (S′ (S′ Z))) · ⊢` (S′ Z)) · ⊢` Z)))))

-- The rest of the Church examples.

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = (((⊢plusᶜ · ⊢twoᶜ) · ⊢twoᶜ) · ⊢sucᶜ) · ⊢zero

-- Lookup is injective (a helper for what follows)

∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′

-- Typing is not injective (e.g identity function).

-- Examples of proofs showing that terms are not typable.

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

-- 747/PLFA exercise: MulTyped (2 points)
-- Show that your mul above is well-typed.
{-
Refine consecutivly.

For the goal "Γ , "*" ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ , "m" ⦂ `ℕ ∋ "m" ⦂ `ℕ", we should use "Z" to refine since the target 
is on the rightmost of the environment list. 

For the goal " "m" ≢ "n" ", we need to assert two string literal are not equal, where we have a 
helper function "_≠_" pre-defined, so we used it here. (Refine has some problems with string literal, 
need rectify the result after refine).

For the goal 
"
Γ , "*" ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ , "m" ⦂ `ℕ , "n" ⦂ `ℕ , "m'" ⦂ `ℕ ⊢
      ` "+" · ` "n" · (` "*" · ` "m'" · ` "n") ⦂ `ℕ
"
To make code clean, we write a helper function in nested where.

When we encounter goals like "..., n ⦂ `ℕ ⊢ n ⦂ A_1098", we just use "Z" and refine.
To make the interactive process smooth, we can complete holes from right to left.
And the final left hole has goal:
"
Γ , "*" ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ , "m" ⦂ `ℕ , "n" ⦂ `ℕ , "m" ⦂ `ℕ ⊢
      plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
", which is exactly the "⊢plus".
-}
⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul {Γ} = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S ("m" ≠ "n")  Z)) ⊢zero helper)))
  where
  helper : Γ , "*" ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ , "m" ⦂ `ℕ , "n" ⦂ `ℕ , "m" ⦂ `ℕ ⊢
      plus · ` "n" · (` "*" · ` "m" · ` "n") ⦂ `ℕ
  helper = ⊢plus · (⊢` (S ("n" ≠ "m") Z)) · (⊢` (S ("*" ≠ "m") (S ("*" ≠ "n") (S ("*" ≠ "m") Z))) · (⊢` Z) · (⊢` (S  ("n" ≠ "m")  Z)))
  
-- 747/PLFA exercise: MulCTyped (2 points)
-- Show that your mulᶜ above is well-typed.
{-
Basically the same idea as the above exercise.
Note that we should not refine goals like " "m" ≢  "n" ".
Instead we should use things like " ("m" ≠ "n") " and refine the hole.
-}
⊢mulᶜ : ∀ {Γ A} → Γ  ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ {Γ} {A} = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ helper)))
  where
  helper : Γ , "m" ⦂ Ch A , "n" ⦂ Ch A , "s" ⦂ A ⇒ A , "z" ⦂ A ⊢ ` "m" · (` "n" · ` "s") · ` "z" ⦂ A
  helper = ⊢` (S ("m" ≠ "z") (S ("m" ≠ "s") (S ("m" ≠ "n") Z))) · (⊢` (S ("n" ≠ "z") (S ("n" ≠ "s") Z)) · (⊢` (S ("s" ≠ "z")   Z))) · (⊢` Z)

-- Unicode:

{-
⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
·  U+00B7  MIDDLE DOT (\cdot)
—  U+2014  EM DASH (\em)
↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
∋  U+220B  CONTAINS AS MEMBER (\ni)
∅  U+2205  EMPTY SET (\0)
⊢  U+22A2  RIGHT TACK (\vdash or \|-)
⦂  U+2982  Z NOTATION TYPE COLON (\:)
😇  U+1F607  SMILING FACE WITH HALO
😈  U+1F608  SMILING FACE WITH HORNS

-}