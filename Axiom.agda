{-# OPTIONS --prop  #-}
module Axiom where

open import LAST
  using (
    Formula; Name; Variable;
    name; var;
    free; sentence; v; v')
open LAST.IdentifierVariable

open import PropUniverses
open import Proposition.Identity hiding (refl)
open import Proposition.Empty
open import Proposition.Permutation
open import Data.Collection
  hiding (_⊆_; ∅) renaming (_∈_ to _is-mem_; _∉_ to _is-not-mem_)
open import Data.List hiding (_++_)
open import Logic hiding (⊥-recursion)

data ZF : 𝒰₁ ˙

Interpretation : (ϕ : Formula) → 𝒰₁ ˙
Interpretation ϕ = (w : Name)(p : w is-mem free ϕ) → ZF

postulate
  _∈_ : (x y : ZF) → 𝒰₁ ᵖ

holds :
  (ϕ : Formula)
  (p : sentence ϕ)
  (i : Interpretation ϕ)
  → --------------------------------------------------------
  𝒰₁ ᵖ
holds (LAST._∈_ {name} {name} x y) p i = x' ∈ y'
  where x' = i x (x∈x∷ [ y ])
        y' = i y (x∈tail x (x∈x∷ []))
holds (LAST._∈_ {name} {var} x y) p i =
  ⊥-recursion (𝒰₁ ᵖ) (p y (x∈x∷ []))
holds (LAST._∈_ {var} x y) p i =
  ⊥-recursion (𝒰₁ ᵖ) (p x (x∈x∷ _))
holds (LAST._≡_ {name} {name} x y) p i = x' == y'
  where x' = i x (x∈x∷ [ y ])
        y' = i y (x∈tail x (x∈x∷ []))
holds (LAST._≡_ {name} {var} x y) p i =
  ⊥-recursion (𝒰₁ ᵖ) (p y (x∈x∷ []))
holds (LAST._≡_ {var} x y) p i =
  ⊥-recursion (𝒰₁ ᵖ) (p x (x∈x∷ _))
holds (ϕ LAST.∨ ψ) p i = {!holds ϕ!}
holds (ϕ LAST.∧ ψ) p i = {!!}
holds (LAST.¬ ϕ) p i = {!¬ holds ϕ p i!}
holds (LAST.A v , ϕ) p i = {!!}
holds (LAST.∃ v , ϕ) p i = {!!}

private
  rep-sentence :
    (ϕ : Formula)
    (p : free ϕ ~ [ v ⸴ v' ])
    → ------------------------
    sentence (LAST.A v , LAST.∃! v' , ϕ)

  rep-interpret :
    (ϕ : Formula)
    (v v' : Variable)
    (i : Interpretation ϕ)
    → ------------------------
    Interpretation (LAST.A v , LAST.∃! v' , ϕ)

data ZF where
  𝒫 ⋃ : (x : ZF) → ZF
  ∅ ∞ : ZF
  rep :
    (ϕ : Formula)
    {vₙ vₘ : Variable}
    (p : free ϕ ~ [ vₙ ⸴ vₘ ])
    (i : Interpretation ϕ)
    (q : holds (LAST.A vₙ , LAST.∃! vₘ , ϕ) (rep-sentence ϕ p) (rep-interpret ϕ vₙ vₘ i))
    (x : ZF)
    → ------------------------
    ZF
  

variable
   x x' x″ y y' y″ z z' z″ : ZF

open import Proposition.Empty
open import Type.Sum hiding (_,_)
open import Data.Collection.Listable.Function
open import Proof

open import Data.Nat

-- two-names : 𝑤 (m +2) is-not-mem [ w₁ ⸴ w₀ ]
-- two-names (xLAST.∈tail w₁ (xLAST.∈tail w₀ ()))

-- one-name :
--   𝑤 (m +1) is-not-mem [ w₀ ]
-- one-name (xLAST.∈tail w₀ ())

-- postulate
--   ZF-ext :
--     holds (F∀ v , F∀ w , v F== w F↔ (F∀ x , x FLAST.∈ v F↔ x FLAST.∈ w ))
--           (λ _ ())
--           (λ _ ())

--   𝒫-def :
--     holds (F∀ v , v FLAST.∈ w₀ F↔ v F⊆ w₁)
--           (λ _ ())
--           λ { w₀ _ → 𝒫 x ;
--               w₁ _ → x ;
--               (𝑤 (_ +2)) p' → ⊥-recursion ZF (two-names p')}

--   ⋃-def :
--     holds (F∀ v , v FLAST.∈ w₀ F↔ (F∃ v' , v' FLAST.∈ w₀ F∧ v FLAST.∈ v'))
--           (λ _ ())
--           λ { w₀ _ → ⋃ x ;
--               (𝑤 (_ +1)) p' → ⊥-recursion ZF (one-name p')}

--   ∅-def : holds (F∀ v , F¬ v FLAST.∈ w₀)
--                 (λ _ ())
--                 λ { w₀ _ → ∅ ;
--                     (𝑤 (_ +1)) p' → ⊥-recursion ZF (one-name p')}

--   ∞-def : holds (w₀ FLAST.∈ w₁ F∧ (F∀ v , v FLAST.∈ w₁ F→ ｛ v ｝FLAST.∈ w₁))
--                 (λ _ ())
--                 λ { w₀ _ → ∅ ;
--                     w₁ _ → ∞ ;
--                    (𝑤 (_ +2)) p' → ⊥-recursion ZF (two-names p')}

-- -- _⊆_ : (x y : ZFZF) → Prop
-- -- x ⊆ y = ∀ a → a LAST.∈ x → x LAST.∈ y

-- -- disjoint : (x y : ZFZF) → Prop
-- -- disjoint x y = ∀ a → ¬ (a LAST.∈ x ∧ a LAST.∈ y)

-- -- postulate
-- --   ∅ : ZFZF
-- --   LAST.∈∅ : ¬ a LAST.∈ ∅

-- -- postulate
-- --   𝒫 : ZFZF → ZFZF
-- --   LAST.∈𝒫 : a LAST.∈ 𝒫 x ↔ a ⊆ x

-- -- postulate
-- --   ⋃ : ZFZF → ZFZF
-- --   LAST.∈⋃ : a LAST.∈ ⋃ x ↔ ∃ λ (y : ZFZF) → y LAST.∈ x ∧ a LAST.∈ y

-- -- postulate
-- --   rep :
-- --     (ϕ : (a b : ZFZF) → LAST)
-- --     (ϕ-prop : ∀ a → ∃! λ (b : ZFZF) → holds (ϕ a b))
-- --     (x : ZFZF)
-- --     → -----------------------------------------------
-- --     ZFZF
-- --   LAST.∈rep :
-- --     (ϕ : (a b : ZFZF) → LAST)
-- --     (ϕ-prop : ∀ a → ∃! λ (b : ZFZF) → holds (ϕ a b))
-- --     → --------------------------------------------
-- --     b LAST.∈ rep ϕ ϕ-prop x ↔ ∃ λ (a : ZFZF) → a LAST.∈ x ∧ holds (ϕ a b)

-- -- postulate
-- --   sub-sel :
-- --     (ϕ : (a : ZFZF) → LAST)
-- --     (x : ZFZF)
-- --     → -------------------------
-- --     ZFZF
-- --   LAST.∈sub-sel :
-- --     (ϕ : (a : ZFZF) → LAST)
-- --     → -----------------------
-- --     a LAST.∈ sub-sel ϕ x ↔ a LAST.∈ x ∧ holds (ϕ a)

-- -- sing : (x : ZFZF) → ZFZF
-- -- sing x = rep {!eq (𝑣 1) x!} (λ _ → x , {!!}) (𝒫 ∅)

-- -- postulate
-- --   ∞ : ZFZF
-- --   ∅LAST.∈∞ : ∅ LAST.∈ ∞
-- --   LAST.∈∞ : a LAST.∈ ∞ → sing a LAST.∈ ∞

-- -- postulate
-- --   found : ∃ λ (a : ZFZF) → a LAST.∈ x ∧ disjoint a x

-- -- postulate
-- --   choice-ZF :
-- --     (x : ZFZF)
-- --     (nonempty : ¬ ∅ LAST.∈ x)
-- --     (pairwise-disjoint : ∀ a b → a LAST.∈ x → b LAST.∈ x → disjoint a b)
-- --     → ---------------------------------------------------------
-- --     ZFZF
-- --   LAST.∈choice-ZF :
-- --     (nonempty : ¬ ∅ LAST.∈ x)
-- --     (pairwise-disjoint : ∀ a b → a LAST.∈ x → b LAST.∈ x → disjoint a b)
-- --     → ----------------
-- --     ∃ λ (f : ZFZF → ZFZF) → 
-- --     (∀ y → y LAST.∈ x → f y LAST.∈ y)
-- --     ∧
-- --     (a LAST.∈ choice-ZF x nonempty pairwise-disjoint ↔ ∃ λ (y : ZFZF) → y LAST.∈ x ∧ a == f y)
