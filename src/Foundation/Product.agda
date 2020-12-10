{-# OPTIONS --exact-split #-}
module Foundation.Product where

open import Foundation.Axiom.Base
open import Foundation.Axiom.ZF
open import Foundation.Pair

open import Data.Product hiding (_×_)

infixl 24 _×_
_×_ : (A B : set) → set
A × B = ｛ x ∈ 𝒫 $ 𝒫 $ A ∪ B ∣ ⋁ a ∈ A , ⋁ b ∈ B , x ≡ ⟨ a ، b ⟩ ｝

private
  variable
    A B : set

abstract
  ∈× : ∀{x} → x ∈ A × B ⇔ (⋁ a ∈ A , ⋁ b ∈ B , x ≡ ⟨ a ، b ⟩)
  ∈× {A}{B} = mk⇔ (proj₂ ∘ from ∈｛ x ∈ U ∣ ϕ x ｝)
    (λ { (a , a∈A , b , b∈B , refl) →
      to ∈｛ x ∈ U ∣ ϕ x ｝ $
      to ∈𝒫
        (λ x∈⟨a,b⟩ → case from ∈⟨,⟩ x∈⟨a,b⟩ of λ
        { (inj₁ refl) → to ∈𝒫 $ λ x∈｛a｝ →
        case from ∈｛ a ｝ x∈｛a｝ of λ
        { refl → to ∈∪ $ inj₁ a∈A }
        ; (inj₂ refl) → to ∈𝒫 $ λ x∈｛a,b｝ →
        case from ∈｛ a ، b ｝ x∈｛a,b｝ of λ
        { (inj₁ refl) → to ∈∪ $ inj₁ a∈A
        ; (inj₂ refl) → to ∈∪ $ inj₂ b∈B } }) ,
      a , a∈A , b , b∈B , refl})
    where U = 𝒫 $ 𝒫 $ A ∪ B
          ϕ = λ x → ⋁ a ∈ A , ⋁ b ∈ B , x ≡ ⟨ a ، b ⟩

