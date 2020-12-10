{-# OPTIONS --exact-split #-}
module ZF.Foundation.Natural.Representation where

open import ZF.Foundation.Axiom.Base
open import ZF.Foundation.Axiom.ZF
open import ZF.Foundation.Natural.Induction

-- synonym to make intention of some types clearer
ℕ : Set
ℕ = set

open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat
open import Data.Unit

instance
  number : Number set
Number.Constraint number _ = ⊤
fromNat ⦃ number ⦄ 0 = ∅
fromNat ⦃ number ⦄ (suc n) = fromNat ⦃ number ⦄ n ⁺

is-nat : (x : set) → Set
is-nat x =
  (x ≡ ∅ ∨ ∃[ y ] (x ≡ y ⁺)) ∧
  (⋀ n ∈ x , n ≡ ∅ ∨ (⋁ y ∈ x , n ≡ y ⁺))

open import Data.Empty
open import Data.Sum

-- abstract
--   -- might require ∈-induction
--   nat∈ω : ∀{x} → x ∈ ω ⇔ is-nat x
--   nat∈ω = mk⇔ is-nat∈ω λ { (fst , snd) → {!!}}
--     where stepcase : ⋀ n ∈ ω , (is-nat n → is-nat (n ⁺))
--           is-nat∈ω = is-nat n
--             by-induction-on n
--             [base: inj₁ refl , ⊥-elim ∘ ∈∅
--             ,step: stepcase
--             ]
--           open import Function.Reasoning
--           proj₁ (stepcase {x} _ _) = inj₂ (x , refl)
--           proj₂ (stepcase x∈ω (inj₁ refl , ∀sub-n)) =
--             inj₁ ∘ fromInj₂ (⊥-elim ∘ ∈∅) ∘ from ∈⁺ 
--           proj₂ (stepcase {x} x∈ω (inj₂ (z , refl) , ∀sub-n)) {y} y∈x⁺ =
--                from ∈⁺ y∈x⁺ ∶ y ∈ x ∨ y ≡ x
--             |> [ map₂ (λ { (k , k∈z⁺ , refl) →
--                        k , to ∈⁺ (inj₁ k∈z⁺) , refl}) ∘
--                  ∀sub-n ,
--                  (λ {refl → inj₂ $
--                      z , to ∈⁺ (inj₁ $ to ∈⁺ $ inj₂ refl) , refl})
--                ] ∶ y ≡ ∅ ∨ (⋁ y' ∈ x ⁺ , y ≡ y' ⁺)
  
            -- inj₂ (x , refl) , λ {y} y∈x⁺ → case x≡∅∨suc , from ∈⁺ y∈x⁺ of λ
            --   { (inj₁ refl , y∈∅∨y≡∅) → inj₁ $ fromInj₂ (⊥-elim ∘ ∈∅) y∈∅∨y≡∅
            --   ; (inj₂ (z , refl) , inj₁ y∈z⁺) →
            --     map₂ (λ { (k , k∈z⁺ , refl) → k , to ∈⁺ (inj₁ k∈z⁺) , refl}) $
            --     ∀sub-n y∈z⁺
            --   ; (inj₂ (z , refl) , inj₂ refl) →
            --     inj₂ (z , to ∈⁺ (inj₁ $ to ∈⁺ $ inj₂ refl) , refl)}
        
--   (λ x∈ω → case from ∈ω x∈ω of λ
--     { (inj₁ refl) → inj₁ refl , λ y∈∅ → ⊥-elim $ ∈∅ y∈∅
--     ; (inj₂ (x' , x'∈ω , refl)) → inj₂ (x' , refl) , λ x∈x'⁺ → {!!}})
--   {!!}
--   λ { (inj₁ refl , _) → ∅∈ω
--     ; (inj₂ (y , refl) , ∀n∈x,nat-n) → prop inductive-ω $
--       case ∀n∈x,nat-n $ to ∈∪ $ inj₂ $ to ∈｛ y ｝ refl of λ
--       { (inj₁ refl) → ∅∈ω
--       ; (inj₂ (x' , _ , refl)) → {!!}}}

-- nat-like is-nat' : (x : set) → Set
-- nat-like x = x ≡ ∅ ∨ (⋁ y ∈ x , x ≡ y ⁺)

-- is-nat' x = nat-like x ∧ (⋀ n ∈ x , nat-like n)

-- -- TODO: think more about this, looks like it might need induction though
-- is-nat⇔is-nat' : ∀{x} → is-nat x ⇔ is-nat' x
-- is-nat⇔is-nat' = {!!}
