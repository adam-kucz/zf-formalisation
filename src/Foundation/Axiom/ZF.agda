{-# OPTIONS --exact-split #-}
module Foundation.Axiom.ZF where

open import Foundation.Axiom.Base

r-prop = (X x y : set) → Set

postulate
  set-ext : ∀ X Y (p : ∀ z → z ∈ X ⇔ z ∈ Y) → X ≡ Y

  ∞-exists : ∃[ ∞ ]
    (nonempty ∞ ∧ (⋀ x ∈ ∞ , ∀ s[x] (q : s[x] =S[ x ]) → s[x] ∈ ∞))

  ⋃-exists : ∀ X → ∃[ ⋃X ] (⋀ y ∈ X , ⋀ z ∈ y , z ∈ ⋃X)

  𝒫-exists : ∀ X → ∃[ 𝒫[X] ] ∀ Z → (p : Z ⊆ X) → Z ∈ 𝒫[X]

  replacement-exists : (ϕ : r-prop) →
    ∀ X (p : ⋀ x ∈ X , ∃! λ y → ϕ X x y)
    → ----------------------------------------
    ∃[ Y ] (⋀ x ∈ X , ⋁ y ∈ Y , ϕ X x y)

  separation : (ϕ : set → Set) → ∀ X → ∃[ Y ] ∀{x} → x ∈ Y ⇔ (x ∈ X ∧ ϕ x)

  regularity :
    ∀ X (p : nonempty X)
    → -------------------------
    ⋁ y ∈ X , ¬ ∃[ z ] (z ∈ X ∧ z ∈ y)

private
  variable
    X Y Z W : set

antisym-⊆ : X ⊆ Y → Y ⊆ X → X ≡ Y
antisym-⊆ {X}{Y} X⊆Y Y⊆X = set-ext X Y λ z → mk⇔ X⊆Y Y⊆X

refl-⊆ : X ⊆ X
refl-⊆ = id

reflexive-⊆ : X ≡ Y → X ⊆ Y
reflexive-⊆ refl = refl-⊆

separation-syntax : (ϕ : set → Set)(X : set) → set
separation-syntax ϕ = elem ∘ separation ϕ

syntax separation-syntax (λ x → ϕ) X = ｛ x ∈ X ∣ ϕ ｝

separation-prop-syntax : (ϕ : set → Set)(X : set) →
  ∀{x} → x ∈ ｛ x ∈ X ∣ ϕ x ｝ ⇔ (x ∈ X ∧ ϕ x)
separation-prop-syntax ϕ = prop ∘ separation ϕ

syntax separation-prop-syntax (λ x → ϕ) X = ｛ x ∈ X ∣ ϕ ｝ₚ

sep⊆ : (ϕ : set → Set)(X : set)
  → ----------------------------------------
  ｛ x ∈ X ∣ ϕ x ｝ ⊆ X
sep⊆ ϕ X x∈sep = proj₁ $ to ｛ x ∈ X ∣ ϕ x ｝ₚ x∈sep

∅ : set
∅ = ｛ x ∈ elem ∞-exists ∣ x ≢ x ｝

∈∅ : ∀{x} → x ∉ ∅
∈∅ {x} x∈∅ =
  proj₂ (to (prop $ separation (λ x → x ≢ x) $ elem ∞-exists) x∈∅) refl

∅⊆ : (X : set) → ∅ ⊆ X
∅⊆ X {x} x∈∅ with () ← ∈∅ x∈∅

𝒫 : (X : set) → set
𝒫 X = ｛ x ∈ elem $ 𝒫-exists X ∣ x ⊆ X ｝

∈𝒫 : ∀ X {x} → x ∈ 𝒫 X ⇔ x ⊆ X
∈𝒫 X {x} =
  mk⇔ (proj₂ ∘ to 𝒫-def) λ x⊆X → from 𝒫-def $ prop (𝒫-exists X) x x⊆X , x⊆X
  where 𝒫-def = ｛ x ∈ elem $ 𝒫-exists X ∣ x ⊆ X ｝ₚ

x∈𝒫[_] : ∀ x → x ∈ 𝒫 x
x∈𝒫[ x ] = from (∈𝒫 x) refl-⊆

∈𝒫∅ : ∀ {x} → x ∈ 𝒫 ∅ → x ≡ ∅
∈𝒫∅ p = antisym-⊆ (to (∈𝒫 ∅) p) (∅⊆ _)

x∉x : ∀{x} → x ∉ x
x∉x {x} x∈x =
  case regularity ｛ y ∈ x ∣ y ≡ x ｝
                  (x , from ｛ y ∈ x ∣ y ≡ x ｝ₚ (x∈x , refl)) of λ
  { (x' , x'∈x , ¬∃) → case proj₂ $ to ｛ y ∈ x ∣ y ≡ x ｝ₚ x'∈x of
    λ {refl → ¬∃ (x' , x'∈x , x∈x)}}

𝒫[x]≢x : ∀{x} → 𝒫 x ≢ x
𝒫[x]≢x {x} 𝒫x≡x = x∉x $ subst (x ∈_) 𝒫x≡x x∈𝒫[ x ]

⋃ : (X : set) → set
⋃ X = ｛ x ∈ elem $ ⋃-exists X ∣ ⋁ y ∈ X , x ∈ y ｝

∈⋃ : ∀ X {x} → x ∈ ⋃ X ⇔ (⋁ Y ∈ X , x ∈ Y)
∈⋃ X {x} = mk⇔ (proj₂ ∘ to ⋃-def)
  λ { p@(y , y∈X , x∈y) → from ⋃-def $ prop (⋃-exists X) y∈X x∈y  , p}
  where ⋃-def = ｛ x ∈ elem $ ⋃-exists X ∣ ⋁ y ∈ X , x ∈ y ｝ₚ

replacement :
  (ϕ : r-prop)
  (X : set)
  (p : ⋀ x ∈ X , ∃! λ y → ϕ X x y) → set
replacement ϕ X p =
  ｛ y ∈ elem $ replacement-exists ϕ X p ∣ ⋁ x ∈ X , ϕ X x y ｝

∈replacement : 
  (ϕ : r-prop)
  (X : set)
  (p : ⋀ x ∈ X , ∃! λ y → ϕ X x y)
  → ----------------------------------------
  ∀{y} → y ∈ replacement ϕ X p ⇔ (⋁ x ∈ X , ϕ X x y)
∈replacement ϕ X p {y} =
  mk⇔ (proj₂ ∘ to replacement-def)
      λ { q@(x , x∈X , ϕXxy) → from replacement-def $
      (case prop r x∈X of λ { (y' , y'∈r , ϕXxy') →
       subst (_∈ elem r) (
         begin y' ≡⟨ sym $ ϕXxy' |> proj₂ (proj₂ $ p x∈X) ⟩
               proj₁ (p x∈X) ≡⟨ ϕXxy |> proj₂ (proj₂ $ p x∈X) ⟩
               y
         ∎) y'∈r}) ,
       q }
  where r = replacement-exists ϕ X p
        replacement-def = ｛ y ∈ elem r ∣ ⋁ x ∈ X , ϕ X x y ｝ₚ
        open ≡-Reasoning

⋂ : (X : set) → set
⋂ X = ｛ x ∈ ⋃ X ∣ ⋀ y ∈ X , x ∈ y ｝

∈⋂ : ∀ X {x} → x ∈ ⋂ X ⇔ (x ∈ ⋃ X ∧ (⋀ Y ∈ X , x ∈ Y))
∈⋂ X {x} = ｛ x ∈ ⋃ X ∣ ⋀ y ∈ X , x ∈ y ｝ₚ
