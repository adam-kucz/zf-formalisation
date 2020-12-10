{-# OPTIONS --exact-split #-}
module ZF.Foundation.Pair.Properties where

open import ZF.Foundation.Axiom
open import ZF.Foundation.Pair.Base

private
  variable A B C X Y Z : set

⋃｛_｝ : ∀ X → ⋃ ｛ X ｝ ≡ X
⋂｛_｝ : ∀ X → ⋂ ｛ X ｝ ≡ X

comm-∪ : A ∪ B ≡ B ∪ A
comm-∩ : A ∩ B ≡ B ∩ A

∅-∪ : ∅ ∪ A ≡ A
∅-∩ : ∅ ∩ A ≡ ∅

idemp-∪ : A ∪ A ≡ A
idemp-∩ : A ∩ A ≡ A

import Data.Sum as Sum
import Data.Product as Prod
open import Data.Empty

abstract
  ⋃｛ X ｝ = antisym-⊆
    (λ x∈⋃｛X｝ → case from ∈⋃ x∈⋃｛X｝ of λ
      { (X' , X'∈｛X｝ , x∈X') → case from ∈｛ X ｝ X'∈｛X｝ of λ
      { refl → x∈X' }})
    (λ x∈X → to ∈⋃ $ X , to ∈｛ X ｝ refl , x∈X)

  ⋂｛ X ｝ = antisym-⊆
    (λ x∈⋂｛X｝ → case from ∈⋃ $ proj₁ $ from ∈⋂ x∈⋂｛X｝ of λ
      { (X' , X'∈｛X｝ , x∈X') → case from ∈｛ X ｝ X'∈｛X｝ of λ
      { refl → x∈X' }})
    (λ x∈X → to ∈⋂ $ to ∈⋃ (X , to ∈｛ X ｝ refl , x∈X) ,
                     λ X'∈｛X｝ → case from ∈｛ X ｝ X'∈｛X｝ of λ
                       { refl → x∈X })

  comm-∪ = antisym-⊆ (to ∈∪ ∘ Sum.swap ∘ from ∈∪)
                     (to ∈∪ ∘ Sum.swap ∘ from ∈∪)
  comm-∩ = antisym-⊆ (to ∈∩ ∘ Prod.swap ∘ from ∈∩)
                     (to ∈∩ ∘ Prod.swap ∘ from ∈∩)

  ∅-∪ = antisym-⊆ (Sum.fromInj₂ (⊥-elim ∘ ∈∅) ∘ from ∈∪)(to ∈∪ ∘ inj₂)
  ∅-∩ {A} = antisym-⊆ (proj₁ ∘ from ∈∩) (∅⊆ $ ∅ ∩ A)

  idemp-∪ = antisym-⊆ (Sum.[ id , id ] ∘ from ∈∪) (to ∈∪ ∘ inj₁)
  idemp-∩ = antisym-⊆ (proj₁ ∘ from ∈∩) (to ∈∩ ∘ Prod.< id , id >)

