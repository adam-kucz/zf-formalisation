{-# OPTIONS --exact-split #-}
module ZF.Foundation.Relation.Reification where

open import ZF.Foundation.Relation.Base
open import ZF.Foundation.Axiom
open import ZF.Foundation.Pair

open import Data.Product hiding (_×_)

private
  variable X Y e x y : set
           ϕ : (x y : set) → Set

abstract
  reify : (X Y : set)(ϕ : (x y : set) → Set) → set
  reify X Y ϕ = ｛ e ∈ X × Y ∣ (∃₂ λ x y → e ≡ ⟨ x ، y ⟩ ∧ ϕ x y ) ｝

  ∈reify : e ∈ reify X Y ϕ ⇔ (∃₂ λ x y → e ≡ ⟨ x ، y ⟩ ∧ x ∈ X ∧ y ∈ Y ∧ ϕ x y)
  ∈reify {e}{X}{Y}{ϕ} = mk⇔
    (λ e∈r → case from ∈r e∈r of λ
    { (e∈X×Y , x , y , refl , ϕ) → case from ⟨,⟩∈× e∈X×Y of λ
    { (x∈X , y∈Y) → x , y , refl , x∈X , y∈Y , ϕ }})
    λ { (x , y , refl , x∈X , y∈Y , ϕ) → to ∈r $
      to ⟨,⟩∈× (x∈X , y∈Y) , x , y , refl , ϕ}
    where ∈r = ∈｛ e ∈ X × Y ∣ (∃₂ λ x y → e ≡ ⟨ x ، y ⟩ ∧ ϕ x y ) ｝

  ⟨,⟩∈reify : ⟨ x ، y ⟩ ∈ reify X Y ϕ ⇔ (x ∈ X ∧ y ∈ Y ∧ ϕ x y)
  ⟨,⟩∈reify {x}{y}{X}{Y}{ϕ} = mk⇔
    (λ xy∈r → case from ∈reify xy∈r of λ
    { (x' , y' , xy≡x'y' , x∈X , y∈Y , ϕ) → case from ⟨,⟩≡ xy≡x'y' of λ
    { (refl , refl) → x∈X , y∈Y , ϕ}})
    λ {(x∈X , y∈Y , ϕ) → to ∈reify $
      x , y , refl , x∈X , y∈Y , ϕ}

  reify-is-rel : reify X Y ϕ ∈ Rel X Y
  reify-is-rel {X}{Y}{ϕ} = to ∈𝒫 $
    sep⊆ (λ e → ∃₂ λ x y → e ≡ ⟨ x ، y ⟩ ∧ ϕ x y ) (X × Y)
  
dereify : (R : set)(x y : set) → Set
dereify R x y = ⟨ x ، y ⟩ ∈ R
