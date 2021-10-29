module 747Lambda where 

open import LambdaRefactor
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Bool using (T; not)
open import Data.String using (String; _≟_) 
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Function using (_∘_)

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

  For the thrid case, double variables case split dose not work!!!
  We just case split on the first variable and in the second case we have a middle term that is not in the scope.
  So we case split on the first variable again to try getting the hidden item. 
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
    trans (l —→⟨ x ⟩ m2 —→⟨ x₁ ⟩ lm) mn = l —→⟨ x ⟩ (m2 —→⟨ x₁ ⟩ (trans lm mn ))

  {-
  Case split.
  For the first case, compute the goal using command C-c C-n got refl.

  For the second case, compute the goal, we got "(t —→⟨ x ⟩ ms1≤ms2-from (ms1≤ms2-to x₁)) ≡ (t —→⟨ x ⟩ x₁)".
  By induction we have "ms1≤ms2-from (ms1≤ms2-to x₁) ≡ x₁", then we got the answer.
  -}
  ms1≤ms2-from∘to : ∀ {P Q} →  (x : P —↠ Q) → (ms1≤ms2-from ∘ ms1≤ms2-to) x ≡ x
  ms1≤ms2-from∘to (_ ∎) = refl
  ms1≤ms2-from∘to (t —→⟨ x ⟩ x₁) rewrite ms1≤ms2-from∘to x₁ = refl


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
To make code clean, we write a helper function in the nested where.

When we encounter goals like "..., n ⦂ `ℕ ⊢ n ⦂ _A_1098", we just use "Z" and refine.
To make the interactive process smooth, we can complete holes from right to left.
And the final left hole has goal:
"
Γ , "*" ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ , "m" ⦂ `ℕ , "n" ⦂ `ℕ , "m" ⦂ `ℕ ⊢
      plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
", which is exactly the "⊢plus".

By the example of "⊢plus", we know that "S′" is better than "S", so we replaced them later.
We find the code of helper function is not so long, then we just copy-paste and removed the helper function.
-}
⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul {Γ} = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S′ Z)) ⊢zero (⊢plus · (⊢` (S′ Z)) · (⊢` (S′ (S′ (S′ Z))) · (⊢` Z) · (⊢` (S′  Z)))))))
  
-- 747/PLFA exercise: MulCTyped (2 points)
-- Show that your mulᶜ above is well-typed.
{-
Basically the same idea as the above exercise.
-}
⊢mulᶜ : ∀ {Γ A} → Γ  ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ {Γ} {A} = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` (S′ (S′ (S′ Z))) · (⊢` (S′ (S′ Z)) · (⊢` (S′ Z))) · (⊢` Z)))))