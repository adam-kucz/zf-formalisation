{-# OPTIONS --prop  #-}
module Axiom where

open import PropUniverses
open import Proposition.Identity using (_==_)
open import LAST
open IdentifierVariable

pattern w₀ = 𝑤 0
pattern w₁ = 𝑤 1
pattern w₂ = 𝑤 2
pattern w₃ = 𝑤 3
pattern v₀ = 𝑣 0
pattern v₁ = 𝑣 1
pattern v₂ = 𝑣 2
pattern v₃ = 𝑣 3

open import Data.List hiding (_++_)
open import Proposition.Permutation
open import Logic hiding (⊥-recursion)
open import Data.Collection
  hiding (_⊆_; ∅) renaming (_∈_ to _is-mem_; _∉_ to _is-not-mem_)

data set : 𝒰₁ ˙

holds :
  (ϕ : Formula)
  (p : sentence ϕ)
  (i : (w : Name)(p' : w is-mem free ϕ) → set)
  → --------------------------------------------------------
  𝒰₀ ᵖ

data set where
  𝒫 ⋃ : (x : set) → set
  ∅ ∞ : set
  -- rep :
  --   (ϕ : Formula)
  --   (p : free ϕ ~ [ v₀ ⸴ v₁ ])
  --   (q : ∀ (a : set) → ∃! λ (b : set) →
  --     holds ϕ {!!} {!!})
  --   (x : set)
  --   → ------------------------
  --   set

｛_｝ : (x : set) → set
｛ x ｝ = 𝒫 x

variable
   x x' x″ y y' y″ z z' z″ : set

open import Proposition.Empty
open import Type.Sum hiding (_,_)
open import Data.Collection.Listable.Function
open import Proof

open import Data.Nat

𝒫-aux : 𝑤 (m +2) is-not-mem free (w₀ F∈ w₁ F↔ w₀ F⊆ w₁)
𝒫-aux (x∈tail w₁ (x∈tail w₀ ()))

one-name :
  𝑤 (m +1) is-not-mem [ w₀ ]
one-name (x∈tail w₀ ())

postulate
  𝒫-def :
    holds (F∀ v , v F∈ w₀ F↔ v F⊆ w₁)
          (λ _ ())
          λ { w₀ _ → 𝒫 x ;
              w₁ _ → x ;
              (𝑤 (_ +2)) p' → ⊥-recursion set (𝒫-aux p')}

  ⋃-def :
    holds (F∀ v , v F∈ w₀ F↔ (F∃ v' , v' F∈ w₀ F∧ v F∈ v'))
          (λ _ ())
          λ { w₀ _ → ⋃ x ;
              (𝑤 (_ +1)) p' → ⊥-recursion set (one-name p')}

  ∅-def : holds (F∀ v , F¬ v F∈ w₀)
                (λ _ ())
                λ { w₀ _ → ∅ ;
                    (𝑤 (_ +1)) p' → ⊥-recursion set (one-name p')}

  ∞-def : holds (w₀ F∈ w₁ F∧ (F∀ v , v F∈ w₁ F→ ｛ v ｝ F∈ w₁))
                (λ _ ())
                λ { w₀ _ → ∅ ;
                    w₁ _ → ∞ ;
                   (𝑤 (_ +2)) p' → ⊥-recursion set (𝒫-aux p')}

-- postulate
--   set-ext : x ≡ y ↔ (∀ a → a ∈ x ↔ a ∈ y )

-- _⊆_ : (x y : ZFSet) → Prop
-- x ⊆ y = ∀ a → a ∈ x → x ∈ y

-- disjoint : (x y : ZFSet) → Prop
-- disjoint x y = ∀ a → ¬ (a ∈ x ∧ a ∈ y)

-- postulate
--   ∅ : ZFSet
--   ∈∅ : ¬ a ∈ ∅

-- postulate
--   𝒫 : ZFSet → ZFSet
--   ∈𝒫 : a ∈ 𝒫 x ↔ a ⊆ x

-- postulate
--   ⋃ : ZFSet → ZFSet
--   ∈⋃ : a ∈ ⋃ x ↔ ∃ λ (y : ZFSet) → y ∈ x ∧ a ∈ y

-- postulate
--   rep :
--     (ϕ : (a b : ZFSet) → LAST)
--     (ϕ-prop : ∀ a → ∃! λ (b : ZFSet) → holds (ϕ a b))
--     (x : ZFSet)
--     → -----------------------------------------------
--     ZFSet
--   ∈rep :
--     (ϕ : (a b : ZFSet) → LAST)
--     (ϕ-prop : ∀ a → ∃! λ (b : ZFSet) → holds (ϕ a b))
--     → --------------------------------------------
--     b ∈ rep ϕ ϕ-prop x ↔ ∃ λ (a : ZFSet) → a ∈ x ∧ holds (ϕ a b)

-- postulate
--   sub-sel :
--     (ϕ : (a : ZFSet) → LAST)
--     (x : ZFSet)
--     → -------------------------
--     ZFSet
--   ∈sub-sel :
--     (ϕ : (a : ZFSet) → LAST)
--     → -----------------------
--     a ∈ sub-sel ϕ x ↔ a ∈ x ∧ holds (ϕ a)

-- sing : (x : ZFSet) → ZFSet
-- sing x = rep {!eq (𝑣 1) x!} (λ _ → x , {!!}) (𝒫 ∅)

-- postulate
--   ∞ : ZFSet
--   ∅∈∞ : ∅ ∈ ∞
--   ∈∞ : a ∈ ∞ → sing a ∈ ∞

-- postulate
--   found : ∃ λ (a : ZFSet) → a ∈ x ∧ disjoint a x

-- postulate
--   choice-set :
--     (x : ZFSet)
--     (nonempty : ¬ ∅ ∈ x)
--     (pairwise-disjoint : ∀ a b → a ∈ x → b ∈ x → disjoint a b)
--     → ---------------------------------------------------------
--     ZFSet
--   ∈choice-set :
--     (nonempty : ¬ ∅ ∈ x)
--     (pairwise-disjoint : ∀ a b → a ∈ x → b ∈ x → disjoint a b)
--     → ----------------
--     ∃ λ (f : ZFSet → ZFSet) → 
--     (∀ y → y ∈ x → f y ∈ y)
--     ∧
--     (a ∈ choice-set x nonempty pairwise-disjoint ↔ ∃ λ (y : ZFSet) → y ∈ x ∧ a == f y)
