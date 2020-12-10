{-# OPTIONS --exact-split #-}
module ZF.Foundation.Axiom.Nonconstructive where

open import ZF.Foundation.Axiom

postulate
  regularity :
    ∀ X (p : nonempty X)
    → -------------------------
    ⋁ y ∈ X , ¬ ∃[ z ] (z ∈ X ∧ z ∈ y)

abstract
  x∉x : ∀{x} → x ∉ x
  x∉x {x} x∈x =
    case regularity ｛ y ∈ x ∣ y ≡ x ｝
                    (_$ to ∈｛ y ∈ x ∣ y ≡ x ｝ $ x∈x , refl) of λ
    { (x' , x'∈x , ¬∃) → case proj₂ $ from ∈｛ y ∈ x ∣ y ≡ x ｝ x'∈x of
      λ {refl → ¬∃ (x' , x'∈x , x∈x)}}
  
  𝒫[x]≢x : ∀{x} → 𝒫 x ≢ x
  𝒫[x]≢x {x} 𝒫x≡x = x∉x $ subst (x ∈_) 𝒫x≡x x∈𝒫[ x ]
  
  open import Level
  open import Axiom.ExcludedMiddle
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Data.Empty
  
  em : ExcludedMiddle 0ℓ
  em {P} = case regularity S (_$ to ∈S $ x∈𝒫[ P1 ] , inj₁ refl) of λ
    { (x , x∈S , ¬∃z∈S∩x) → case from ∈S x∈S of λ
      { (_ , inj₁ refl) → no $ contraposition P→∅∈S λ ∅∈S →
        ¬∃z∈S∩x (∅ , ∅∈S , x∈𝒫[ ∅ ])
      ; (_ , inj₂ p) → yes p}}
    where P1 = 𝒫 ∅
          P2 = 𝒫 P1 -- {∅ , {∅}}
          S = ｛ x ∈ P2 ∣ x ≡ P1 ∨ P ｝
          ∈S = ∈｛ x ∈ P2 ∣ x ≡ P1 ∨ P ｝
          P→∅∈S : P → ∅ ∈ S
          P→∅∈S p = to ∈S (to ∈𝒫 (∅⊆ P1) , inj₂ p)

  open import Axiom.DoubleNegationElimination
  
  is? : (P : Set) → Dec P
  is? P = em {P = P}
  dne = em⇒dne em
  by-contradiction = dne
  
  ¬∀→∃¬ : {P : set → Set}(p : ¬ ∀ x → P x) → ∃[ x ] (¬ P x)
  ¬∀→∃¬ {P} p = by-contradiction λ ¬∃¬P →
    p λ x → by-contradiction λ ¬Px → ¬∃¬P $ x , ¬Px
