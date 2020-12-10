{-# OPTIONS --exact-split #-}
module Foundation.Axiom.ZF where

open import Foundation.Axiom.Base

r-prop = (x y : set) → Set

is-func : (ϕ : r-prop)(X : set) → Set
is-func ϕ X = ⋀ x ∈ X , ∃! λ y → ϕ x y

postulate
  set-ext : ∀ X Y (p : ∀ z → z ∈ X ⇔ z ∈ Y) → X ≡ Y

  ∞-exists : ∃ λ ∞ →
    (∃ λ ∅ → empty ∅ ∧ ∅ ∈ ∞) ∧
    (⋀ x ∈ ∞ , ∀ s[x] (q : s[x] =S[ x ]) → s[x] ∈ ∞)

  ⋃-exists : ∀ X → ∃[ ⋃X ] (⋀ y ∈ X , ⋀ z ∈ y , z ∈ ⋃X)

  𝒫-exists : ∀ X → ∃[ 𝒫[X] ] ∀ Z → (p : Z ⊆ X) → Z ∈ 𝒫[X]

  replacement-exists : (ϕ : r-prop) →
    ∀ X (p : is-func ϕ X)
    → ----------------------------------------
    ∃[ Y ] (⋀ x ∈ X , ⋁ y ∈ Y , ϕ x y)

  separation : (ϕ : set → Set) → ∀ X → ∃[ Y ] ∀{x} → x ∈ Y ⇔ (x ∈ X ∧ ϕ x)

separation-syntax : (ϕ : set → Set)(X : set) → set
separation-syntax ϕ = elem ∘ separation ϕ

syntax separation-syntax (λ x → ϕ) X = ｛ x ∈ X ∣ ϕ ｝

abstract
  separation-prop-syntax : (ϕ : set → Set)(X : set) →
    ∀{x} → x ∈ ｛ x ∈ X ∣ ϕ x ｝ ⇔ (x ∈ X ∧ ϕ x)
  separation-prop-syntax ϕ = prop ∘ separation ϕ

syntax separation-prop-syntax (λ x → ϕ) X = ∈｛ x ∈ X ∣ ϕ ｝

∅ : set
∅ = ｛ x ∈ elem ∞-exists ∣ x ≢ x ｝

𝒫 : (X : set) → set
𝒫 X = ｛ x ∈ elem $ 𝒫-exists X ∣ x ⊆ X ｝

abstract
  ∈𝒫 : ∀{X x} → x ∈ 𝒫 X ⇔ x ⊆ X
  ∈𝒫 {X} {x} =
    mk⇔ (proj₂ ∘ from 𝒫-def)
        λ x⊆X → to 𝒫-def $ prop (𝒫-exists X) x x⊆X , x⊆X
    where 𝒫-def = ∈｛ x ∈ elem $ 𝒫-exists X ∣ x ⊆ X ｝


⋃ : (X : set) → set
⋃ X = ｛ x ∈ elem $ ⋃-exists X ∣ ⋁ y ∈ X , x ∈ y ｝

abstract
  ∈⋃ : ∀{X x} → x ∈ ⋃ X ⇔ (⋁ Y ∈ X , x ∈ Y)
  ∈⋃ {X} {x} = mk⇔ (proj₂ ∘ from ⋃-def)
    λ { p@(y , y∈X , x∈y) → to ⋃-def $ prop (⋃-exists X) y∈X x∈y  , p}
    where ⋃-def = ∈｛ x ∈ elem $ ⋃-exists X ∣ ⋁ y ∈ X , x ∈ y ｝

replacement : ∀
  (ϕ : r-prop)
  {X}
  (p : ⋀ x ∈ X , ∃! (ϕ x)) → set
replacement ϕ {X} p =
  ｛ y ∈ elem $ replacement-exists ϕ X p ∣ ⋁ x ∈ X , ϕ x y ｝

abstract
  ∈replacement : 
    (ϕ : r-prop)
    {X : set}
    (p : ⋀ x ∈ X , ∃! λ y → ϕ x y)
    → ----------------------------------------
    ∀{y} → y ∈ replacement ϕ p ⇔ (⋁ x ∈ X , ϕ x y)
  ∈replacement ϕ {X} p {y} =
    mk⇔ (proj₂ ∘ from replacement-def)
        λ { q@(x , x∈X , ϕXxy) → to replacement-def $
        (case prop r x∈X of λ { (y' , y'∈r , ϕXxy') →
         subst (_∈ elem r) (
           begin y' ≡⟨ sym $ ϕXxy' |> proj₂ (proj₂ $ p x∈X) ⟩
                 proj₁ (p x∈X) ≡⟨ ϕXxy |> proj₂ (proj₂ $ p x∈X) ⟩
                 y
           ∎) y'∈r}) ,
         q }
    where r = replacement-exists ϕ X p
          replacement-def = ∈｛ y ∈ elem r ∣ ⋁ x ∈ X , ϕ x y ｝
          open ≡-Reasoning

⋂ : (X : set) → set
⋂ X = ｛ x ∈ ⋃ X ∣ ⋀ y ∈ X , x ∈ y ｝

abstract
  ∈⋂ : ∀{X x} → x ∈ ⋂ X ⇔ (x ∈ ⋃ X ∧ (⋀ Y ∈ X , x ∈ Y))
  ∈⋂ {X} {x} = ∈｛ x ∈ ⋃ X ∣ ⋀ y ∈ X , x ∈ y ｝
