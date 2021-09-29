module 747Isomorphism where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym) -- added last
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc; +-identityʳ) -- added last

-- Function composition.

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Another definition of addition.

_+′_ : ℕ → ℕ → ℕ -- split on n instead, get different code
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_  -- this requires extensionality
same = extensionality (λ m → extensionality (λ n → same-app m n))

-- Isomorphism.

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  constructor mk-≃  -- This has been added, not in PLFA
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

-- Equivalent to the following:

data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B)
                         → (∀ (x : A)
                         → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B)
                         → (∀ (y : B)
                         → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

-- End of equivalent formulation (records are faster!)

-- Properties of isomorphism.

-- Reflexivity.

≃-refl : ∀ {A : Set}
    -----
  → A ≃ A

-- in empty hole, split on result, get copatterns (not in PLFA)

≃-refl = 
 record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }

-- Symmetry.

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A

≃-sym A≃B = 
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

-- Transitivity.

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C

≃-trans A≃B B≃C = 
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }

-- Isomorphism is an equivalence relation.
-- We can create syntax for equational reasoning.

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

-- Embedding (weaker than isomorphism)

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = 
    record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C = 
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B

≲-antisym A≲B B≲A to≡from from≡to = 
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }

-- Tabular reasoning for embedding.

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- PLFA exercise: Isomorphism implies embedding.
{--
Just case split (on null variable), we get three cases.
Frist hole: Split null again, we got implicit variable x: A, and goal: B, context: a≃b : A ≃ B
See equivalence of "to": to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B), we can infer that "to" transforms "A ≃ B" into a function, 
which can transform "A" into "B", so "(to a≃b)" is a function: A → B, and then we apply "x" to the function, finally we get "B".
Second hole: similar idea as the first case.
Third hole: goal: from a≃b (to a≃b x) ≡ x, context dost not change. From the goal and signature of from∘to : ∀ (x : A) → from (to x) ≡ x,
we can infer that we must utilize "from∘to". We guess that third case maybe has similar prove structure of first two cases,
so we tried "(from∘to a≃b) x" and find it actually works!
--}
≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B  

to (≃-implies-≲ a≃b) x = (to a≃b) x
from (≃-implies-≲ a≃b) x = (from a≃b) x
from∘to (≃-implies-≲ a≃b) x = (from∘to a≃b) x

-- PLFA exercise: propositional equivalence (weaker than embedding).

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_ -- added

-- This is also an equivalence relation.

⇔-refl : ∀ {A : Set}
    -----
  → A ⇔ A

to ⇔-refl x = x -- no context, so we case split on null. Then we have goal: A, context  x: A, obviously we should fill x in the hole.
from ⇔-refl x = x -- same as above case

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
-- Case split on null, we got two cases. This case has goal: "B → A", which is output of "from", 
-- and context: A⇔B : A ⇔ B, then answer is obvious since we know "to" and "from" are functions which input is A ⇔ B and output is corresponding signature.
to (⇔-sym A⇔B) = from A⇔B 
-- The second case has similar idea above.
from (⇔-sym A⇔B) = to A⇔B

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
{--
Still we case split on null since we do not want induction, because it dose not work in this case.
The First hole has goal: A → C, which is a function type.
We split on null again to extract variable x since I do not prefer lambda function.
Then the goal now is C
Since we have context B⇔C : B ⇔ C, A⇔B : A ⇔ B, we can get type B → C and A → B by "to", 
Then connect these two function types, we get function type A → C, then we input A to convert it to C, which is the goal. 
--}
to (⇔-trans A⇔B B⇔C) x = ((to B⇔C) ∘ (to A⇔B)) x 
-- The second case has similar idea.
from (⇔-trans A⇔B B⇔C) x = ((from A⇔B) ∘ (from B⇔C)) x

-- 747/PLFA extended exercise: Canonical bitstrings.
-- Modified and extended from Bin-predicates exercise in PLFA Relations.

-- Copied from 747Naturals.

data Bin-ℕ : Set where
  bits : Bin-ℕ
  _x0 : Bin-ℕ → Bin-ℕ
  _x1 : Bin-ℕ → Bin-ℕ

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

-- Copy your versions of 'inc', 'tob', and 'fromb' over from earlier files.
-- You may choose to change the definitions here to make proofs easier.
-- But make sure to test them if you do!
-- You may also copy over any theorems that prove useful.

inc : Bin-ℕ → Bin-ℕ
inc bits = bits x1 
inc (other x0) = (other x1) 
inc (other x1) = ((inc other) x0) 

tob : ℕ → Bin-ℕ
tob zero =  bits 
tob (suc m) =  inc (tob m) 

dblb : Bin-ℕ → Bin-ℕ
dblb bits = bits
dblb (m x0) = m x0 x0
dblb (m x1) = m x1 x0

fromb : Bin-ℕ → ℕ
fromb bits = zero
fromb (n x0) = dbl (fromb n)  
fromb (n x1) = suc (dbl (fromb n))

-- The reason that we couldn't prove ∀ {n : Bin-ℕ} → tob (fromb n) ≡ n
-- is because of the possibility of leading zeroes in a Bin-ℕ value.
-- 'bits x0 x0 x1' is such a value that gives a counterexample.
-- However, the theorem is true is true for n without leading zeroes.
-- We define a predicate to be able to state this in a theorem.
-- A value of type One n is evidence that n has a leading one.

data One : Bin-ℕ → Set where
  [bitsx1] : One (bits x1)
  _[x0] : ∀ {n : Bin-ℕ} → One n → One (n x0)
  _[x1] : ∀ {n : Bin-ℕ} → One n → One (n x1)

-- Here's a proof that 'bits x1 x0 x0' has a leading one.

_ : One (bits x1 x0 x0)
_ = [bitsx1] [x0] [x0]

-- There is no value of type One (bits x0 x0 x1).
-- But we can't state and prove this yet, because we don't know
-- how to express negation. That comes in the Connectives chapter.

-- A canonical binary representation is either zero or has a leading one.

data Can : Bin-ℕ → Set where
  [zero] : Can bits
  [pos]  : ∀ {n : Bin-ℕ} → One n → Can n

-- Some obvious examples:

_ : Can bits
_ = [zero]

_ : Can (bits x1 x0)
_ = [pos] ([bitsx1] [x0])

-- The Bin-predicates exercise in PLFA Relations gives three properties of canonicity. 
-- The first is that the increment of a canonical number is canonical.

-- Most of the work is done in the following lemma.

-- 747/PLFA exercise: IncCanOne (2 points)
-- The increment of a canonical number has a leading one.

one-inc : ∀ {n : Bin-ℕ} → Can n → One (inc n)
one-inc [zero] = [bitsx1]  -- Goal: One (bits x1), which is exactly constructor "[bitsx1]"
--We need to case split variable below since we have no other information for proving.
one-inc ([pos] [bitsx1]) = [bitsx1] [x0] -- Goal: One ((bits x1) x0), which is a specific number. We just get answer from constructor of type One
one-inc ([pos] (x [x0])) = x [x1] -- Goal: One (n x1) and context x : One n, which can be transformed into the goal by appending x1.
one-inc ([pos] (x [x1])) = one-inc ([pos] x) [x0] -- Goal: One (inc n x0) and context x : One n, 
-- by induction we already have One (inc n), which can be transformed into the goal by appending x0.
-- By the way, all cases above can be solved by C-c C-a

-- The first canonicity property is now an easy corollary.

-- 747/PLFA exercise: OneInc (1 point)
{--
Case split on cn and then case split on x, we then get four cases.
The first three cases is trivial since they all can be solved by C-c C-a. 
For the fourth cases, we have goal: Can (inc n x0) and context: x : One n.
To get "inc n x0", we should first get "inc n" and then append x0.
The only method to get "inc n" is one-inc, which input is type Can.
So we use "[pos]" to convert x to type "Can" and then apply "one-inc".
Now we have "(one-inc ([pos] x)) : One (inc n)", we then append x0,
and then we have "(one-inc ([pos] x)) [x0] : One (inc n x0)".
Finally, we use "[pos]" to convert type "One" into type "Can", then 
we get "[pos] ((one-inc ([pos] x)) [x0]) : Can (inc n x0)", which is the goal. 
--}

can-inc : ∀ {n : Bin-ℕ} → Can n → Can (inc n)
can-inc [zero] = [pos] [bitsx1]
can-inc ([pos] [bitsx1]) = [pos] ([bitsx1] [x0])
can-inc ([pos] (x [x0])) = [pos] (x [x1])
can-inc ([pos] (x [x1])) = [pos] ((one-inc ([pos] x)) [x0])

-- The second canonicity property is that converting a unary number
-- to binary produces a canonical number.

-- 747/PLFA exercise: CanToB (1 point)
{--
The First case is trivial since it can be solved by C-c C-a.
For the second case, we have goal: Can (inc (tob n)).
By induction we have "to-can n : Can (tob n)".
From signature of "tob" we know that "tob b : Bin-ℕ", which is exactly input type of can-inc.
We apply "can-inc" to the induction, then we get the answer.
--}

to-can : ∀ (n : ℕ) → Can (tob n)
to-can zero = [zero]
to-can (suc n) = can-inc (to-can n)

-- The third canonicity property is that converting a canonical number
-- from binary and back to unary produces the same number.

-- This takes more work, and some helper lemmas from 747Induction.
-- You will need to discover which ones.

-- 747/PLFA exercise: OneDblbX0 (1 point)

-- This helper function relates binary double to the x0 constructor,
-- for numbers with a leading one.
{--
After case split, we find that all cases are refl.
Since it is very easy to prove this way, we dose not choose to find simpler solution.
--}

dblb-x0 : ∀ {n : Bin-ℕ} → One n → dblb n ≡ n x0
dblb-x0 [bitsx1] = refl
dblb-x0 (on [x0]) = refl
dblb-x0 (on [x1]) = refl

-- We can now prove the third property for numbers with a leading one.

-- 747/PLFA exercise: OneToFrom (3 points)

dblb∘inc : ∀ (m : Bin-ℕ) → dblb (inc m) ≡ inc (inc (dblb m)) 
dblb∘inc bits = refl
dblb∘inc (m x0) = refl
dblb∘inc (m x1) = refl

to∘dbl : ∀ (m : ℕ) → tob (dbl m) ≡ dblb (tob m)
to∘dbl zero = refl
to∘dbl (suc m) rewrite to∘dbl m = sym (dblb∘inc (tob m))

-- With this helper function we can get the implicit argument "n", which is very very very... important!
to∘dbl∘fromb≡dblb∘tob∘fromb : ∀{n : Bin-ℕ} → One n → tob (dbl (fromb n)) ≡ dblb (tob (fromb n))
to∘dbl∘fromb≡dblb∘tob∘fromb {n} on rewrite to∘dbl (fromb n) = refl

{--
Case split then we find the first case is trivial.

For the second hole, we have goal: tob (dbl (fromb n)) ≡ (n x0), which we guess that it must utilize the rule of "dblb-x0".
And by induction we already have "tob (fromb n) ≡ n", to utilize both two facts, we should have "tob (dbl (fromb n)) ≡ dblb (tob (fromb n))".
Becase we then by induction reduce left term to "dblb n", then the goal becomes "dblb n ≡ n x0", which is exactly the rule "dblb-x0".
Since we already have hint which tells us we need a helper function from 747Induction, we selected the right one and paste above.

The third case has quite similar idea of the second case.
--}

one-to∘from : ∀ {n : Bin-ℕ} → One n → tob (fromb n) ≡ n
one-to∘from [bitsx1] = refl
one-to∘from (on [x0]) rewrite to∘dbl∘fromb≡dblb∘tob∘fromb on | one-to∘from on  = dblb-x0 on 
one-to∘from (on [x1]) rewrite to∘dbl∘fromb≡dblb∘tob∘fromb on | one-to∘from on | dblb-x0 on = refl

-- The third property is now an easy corollary.

-- 747/PLFA exercise: CanToFrom (1 point)
{--
After case split, the first case is trivial and the second case is obviously the function "one-to∘from".

--}
can-to∘from : ∀ {n : Bin-ℕ} → Can n → tob (fromb n) ≡ n
can-to∘from [zero] = refl
can-to∘from ([pos] x) = one-to∘from x

-- 747/PLFA exercise: OneUnique (2 points)
-- Proofs of positivity are unique.
{--
Case split both variable because we need knowledge both of variables, then we got three cases.
The first case is trival since it is refl.
The second case has goal: (x [x0]) ≡ (y [x0]), context x : One n, y : One n.
By induction we have x ≡ y, after rewrite induction rule we get refl.
The thrid case has quite similar idea.
--}
one-unique : ∀ {n : Bin-ℕ} → (x y : One n) → x ≡ y
one-unique [bitsx1] [bitsx1] = refl
one-unique (x [x0]) (y [x0]) rewrite one-unique x y = refl
one-unique (x [x1]) (y [x1]) rewrite one-unique x y = refl

-- 747/PLFA exercise: CanUnique (1 point)
-- Proofs of canonicity are unique.
{--
Case split both variable because we need knowledge both of variables, then we got two cases.
The first case is trival since its goal is refl.
The second case has goal: [pos] x ≡ [pos] x₁, where x and x₁ is type One n.
So here we need the rule "one-unique" because "can-unique" input type is "Can n".
After rewrite we got refl in the second case.
--}

can-unique : ∀ {n : Bin-ℕ} → (x y : Can n) → x ≡ y
can-unique [zero] [zero] = refl
can-unique ([pos] x) ([pos] x₁) rewrite one-unique x x₁ = refl

-- Do we have an isomorphism between ℕ (unary) and canonical binary representations?
-- Can is not a set, but a family of sets, so it doesn't quite fit
-- into our framework for isomorphism.
-- But we can roll all the values into one set which is isomorphic to ℕ.

-- A CanR value wraps up a Bin-ℕ and proof it has a canonical representation.

record CanR : Set where
  constructor mk-CanR
  field
    n : Bin-ℕ
    cpf : Can n

-- We can show that there is an isomorphism between ℕ and CanR.

-- 747/PLFA exercise: Rewrap (1 point)
-- This helper will be useful.
{--
Case split on null, we got three variables.
Goal: mk-CanR m x ≡ mk-CanR n y
Since we have m ≡ n, by rewrite we eliminate the difference between m and n in the goal. 
Then goal becomes "mk-CanR lhs x ≡ mk-CanR lhs y".
Since we have had the rule can-unique, we can eliminate the difference between x and y by rewrite.
Then we got two same terms in both sides, which is refl.
--}

rewrap : ∀ {m n} x y → m ≡ n → mk-CanR m x ≡ mk-CanR n y
rewrap x y x₁ rewrite x₁ | can-unique x y = refl

-- 747/PLFA exercise: IsoNCanR (2 points)

from∘inc : ∀ (m : Bin-ℕ) → fromb (inc m) ≡ suc (fromb m)
from∘inc bits = refl
from∘inc (m x0) = refl
from∘inc (m x1) rewrite from∘inc m = refl

from∘tob : ∀ (m : ℕ) → fromb (tob m) ≡ m
from∘tob zero = refl
from∘tob (suc m) rewrite from∘inc (tob m) | from∘tob m = refl

{--
Basically, there we need to build projection relation between type CanR and type ℕ.
Split on null we then get four cases which is required by the definition of ≃.
For the first case, we need build CanR from ℕ, CanR has two fields, which are type Bin-ℕ and type Can.
So we just convert ℕ to Bin-ℕ and to Can, and then using the constructor of Can. Then we solved this case.

For the second case, we can get Bin-ℕ from x : CanR using destructor n, which should be prefixed with CanR since it is not open.
Then we use fromb to convert Bin-ℕ to ℕ, then we get the goal.

The goal of thrid case is exactly the exercise of 747Induction, so we just copy and paste above.

In the fourth case we have to split after we have tested other ways of prove.
After case split, it is clear that we can using the helper function "rewrap" above.
According to the signature of rewrap and the context, we have the first two arguments of rewrap.
Now we need only to build the thrid argument, which can be built by function "can-to∘from". 
Then we got the answer.
--}

iso-ℕ-CanR : ℕ ≃ CanR
to iso-ℕ-CanR x = mk-CanR (tob x) (to-can x)
from iso-ℕ-CanR x = fromb (CanR.n x)
from∘to iso-ℕ-CanR x = from∘tob x
to∘from iso-ℕ-CanR (mk-CanR n cpf) rewrite rewrap (to-can (fromb n)) cpf (can-to∘from cpf) = refl

-- Can we get an isomorphism between ℕ and some binary encoding,
-- without the awkwardness of non-canonical values?
-- Yes: we use digits 1 and 2, instead of 0 and 1 (multiplier/base is still 2).
-- This is known as bijective binary numbering.
-- The counting sequence goes <empty>, 1, 2, 11, 12, 21, 22, 111...

data Bij-ℕ : Set where
  bits : Bij-ℕ
  _x1 : Bij-ℕ → Bij-ℕ
  _x2 : Bij-ℕ → Bij-ℕ

-- There is an isomorphism between ℕ and Bij-ℕ.
-- The proof largely follows the outline of what we did above,
-- and is left as an optional exercise.

-- See PLFA for remarks on standard library definitions similar to those here.

-- Unicode introduced in this chapter:

{-

  ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
  λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
  ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
  ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
  ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)

-}