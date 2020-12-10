{-# OPTIONS --exact-split #-}
module Foundation.Axiom.Properties where

open import Foundation.Axiom.Base
open import Foundation.Axiom.ZF

private
  variable
    X Y Z W : set

abstract
  antisym-⊆ : X ⊆ Y → Y ⊆ X → X ≡ Y
  antisym-⊆ {X}{Y} X⊆Y Y⊆X = set-ext X Y λ z → mk⇔ X⊆Y Y⊆X

  refl-⊆ : X ⊆ X
  refl-⊆ = id

  reflexive-⊆ : X ≡ Y → X ⊆ Y
  reflexive-⊆ refl = refl-⊆

  ∈∅ : ∀{x} → x ∉ ∅
  ∈∅ {x} x∈∅ =
    proj₂ (from (prop $ separation (λ x → x ≢ x) $ elem ∞-exists) x∈∅) refl

  ∅⊆ : (X : set) → ∅ ⊆ X
  ∅⊆ X {x} x∈∅ with () ← ∈∅ x∈∅

  x∈𝒫[_] : ∀ x → x ∈ 𝒫 x
  x∈𝒫[ x ] = to ∈𝒫 refl-⊆

  ∈𝒫∅ : ∀ {x} → x ∈ 𝒫 ∅ → x ≡ ∅
  ∈𝒫∅ p = antisym-⊆ (from ∈𝒫 p) (∅⊆ _)

  sep⊆ : (ϕ : set → Set)(X : set)
    → ----------------------------------------
    ｛ x ∈ X ∣ ϕ x ｝ ⊆ X
  sep⊆ ϕ X x∈sep = proj₁ $ from ∈｛ x ∈ X ∣ ϕ x ｝ x∈sep

  open import Data.Empty

  ⋃∅ : ⋃ ∅ ≡ ∅
  ⋃∅ = antisym-⊆ (⊥-elim ∘ ∈∅ ∘ proj₁ ∘ proj₂ ∘ from ∈⋃) (∅⊆ $ ⋃ ∅)

  sep∅ : (ϕ : set → Set) → ｛ x ∈ ∅ ∣ ϕ x ｝ ≡ ∅
  sep∅ ϕ = antisym-⊆ (sep⊆ ϕ ∅) (∅⊆ ｛ x ∈ ∅ ∣ ϕ x ｝)

  ⋂∅ : ⋂ ∅ ≡ ∅
  ⋂∅ = begin ⋂ ∅              ≡⟨ cong (λ X → ｛ x ∈ X ∣ ϕ x ｝) ⋃∅ ⟩
             ｛ x ∈ ∅ ∣ ϕ x ｝ ≡⟨ sep∅ ϕ ⟩
             ∅
       ∎
    where ϕ = λ x → ⋀ y ∈ ∅ , x ∈ y
          open ≡-Reasoning
