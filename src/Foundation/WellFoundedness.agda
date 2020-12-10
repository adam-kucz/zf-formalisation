{-# OPTIONS --exact-split #-}
module Foundation.WellFoundedness where

open import Foundation.Axiom.Base
open import Foundation.Axiom.ZF
open import Foundation.Axiom.Nonconstructive

private variable S X : set

abstract
  ∈-well-founded :
    {S : set}
    (S≢∅ : nonempty S)
    → ----------------------------------------
    ⋁ min ∈ S , ⋀ x ∈ S , ¬ x ∈ min
  ∈-well-founded {S} S≢∅ with regularity S S≢∅
  ... | min , min∈S , ¬x∈min-∩-S =
    min , min∈S , λ {x} x∈S x∈min → ¬x∈min-∩-S (x , x∈S , x∈min)

open import Foundation.Function
open import Foundation.Natural
open import Foundation.RecursiveDefinition

deep⋃ : (X : set) → set
deep⋃ X = ⋃ (ran f)
  where open RecDef (_≡ X)(λ _ y z → z ≡ ⋃ y)
                    (X , refl , sym)(λ _ y → ⋃ y , refl , sym)

module _ {X} where
  open RecDef (_≡ X)(λ _ y z → z ≡ ⋃ y)
              (X , refl , sym)(λ _ y → ⋃ y , refl , sym)
  open import Function.Reasoning

  abstract
    transitive-deep⋃ : transitive (deep⋃ X)
    transitive-deep⋃ {x} x∈deep⋃ {y} y∈x = case from ∈⋃ x∈deep⋃ of λ
      { (v , v∈ran , x∈v) → case from ∈ran v∈ran of λ
      { (n , nv∈f) → case to (f-is-fun [ n ]≡ v) nv∈f of λ
      { (n∈domf , refl) → let n∈ω = subst (n ∈_) f-dom n∈domf
                              n⁺∈ω = to ∈ω $ inj₂ (n , n∈ω , refl)
      in to ∈⋃ $
         ⋃ (f [ n ]) ,
         to ∈ran (n ⁺ , from (f-is-fun [ n ⁺ ]≡ ⋃ (f [ n ]))
                             (subst (n ⁺ ∈_) (sym f-dom) n⁺∈ω , f[x⁺] n∈ω)) ,
         to ∈⋃ (x , x∈v , y∈x)}}}

open import Foundation.Pair

∈-induction : (P : set → Set) →
  (is : ∀ n → (⋀ k ∈ n , P k) → P n)
  → ----------------------------------------
  ∀ n → P n
∈-induction P is = by-contradiction λ ¬∀ → case ¬∀→∃¬ ¬∀ of λ
  { (x , ¬Px) →
    let S = ｛ y ∈ deep⋃ ｛ x ｝ ∣ ¬ P y ｝
        ∈S = ∈｛ y ∈ deep⋃ ｛ x ｝ ∣ ¬ P y ｝
        X = ｛ x ｝
        open RecDef (_≡ X)(λ _ y z → z ≡ ⋃ y)
                    (X , refl , sym)(λ _ y → ⋃ y , refl , sym)
        x∈S = to ∈S $
          to ∈⋃ (｛ x ｝ ,
                 to ∈ran (∅ , from (f-is-fun [ ∅ ]≡ ｛ x ｝)
                                   (subst (∅ ∈_) (sym f-dom) ∅∈ω , f[0])) ,
                 to ∈｛ x ｝ refl) ,
          ¬Px
        nonempty-S : nonempty S
        nonempty-S = inhabited→nonempty (x , x∈S)
    in case ∈-well-founded nonempty-S of λ
    { (min , min∈S , ∀k∈S,k∉min) →
    case from ∈S min∈S of λ
    {(min∈deep⋃ , ¬Pmin) → ¬Pmin $
    is min λ {k} k∈min → by-contradiction λ ¬Pk →
    ∀k∈S,k∉min (to ∈S (transitive-deep⋃ min∈deep⋃ k∈min , ¬Pk)) k∈min}}}
