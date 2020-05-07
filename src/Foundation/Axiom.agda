{-# OPTIONS --prop --exact-split #-}
module Foundation.Axiom where

open import PropUniverses
open import Proposition.Identity
open import Logic hiding (_,_; ⟶)

infix 135 _∈_
postulate
  set : 𝒰₀ ˙
  _∈_ : (x y : set) → 𝒰₀ ᵖ

exists-∈ forall-∈ : (x : set)(ϕ : set → 𝒰 ᵖ) → 𝒰 ᵖ
exists-∈ x ϕ = ∃ λ y → y ∈ x ∧ ϕ y
forall-∈ x ϕ = ∀ y → y ∈ x → ϕ y

infixl 11 exists-∈ forall-∈
syntax exists-∈ x (λ y → ϕ) = ⋁ y ∈ x , ϕ
syntax forall-∈ x (λ y → ϕ) = ⋀ y ∈ x , ϕ

infix 135 _∉_ _⊆_
_∉_ _⊆_ disjoint : (x y : set) → 𝒰₀ ᵖ
x ∉ y = ¬ x ∈ y
x ⊆ y = ⋀ z ∈ x , z ∈ y
disjoint x y = ∀ z → ¬ (z ∈ x ∧ z ∈ y)

_==∅ _≠∅ : (x : set) → 𝒰₀ ᵖ
x ==∅ = ∀ y → y ∉ x
x ≠∅ = ¬ x ==∅

postulate
  set-ext :
    ∀ x y
    (p : ∀ z → z ∈ x ↔ z ∈ y)
    → -----------------------
    x == y

  separation :
    ∀ (ϕ : set → 𝒰 ᵖ)
    x →
    ∃ λ y →
    ∀ u →
    u ∈ y ↔ u ∈ x ∧ ϕ u

  ⋃-exists :
    ∀ x →
    ∃ λ ⋃x →
    ⋀ y ∈ x ,
    ⋀ z ∈ y ,
    z ∈ ⋃x

  𝒫-exists :
    ∀ x →
    ∃ λ 𝒫[x] →
    ∀ z →
    (p : z ⊆ x)
    → ------------
    z ∈ 𝒫[x]

_=S[_] : (y x : set) → 𝒰₀ ᵖ
y =S[ x ] = ∀ z → z ∈ y ↔ z ∈ x ∨ z == x

postulate
  ∞-exists :
    ∃ λ x →
    (∀ y (p : y ==∅) → y ∈ x)
    ∧
    (⋀ y ∈ x , ∀ z (q : z =S[ y ]) → z ∈ x)

  replacement :
    ∀ (ϕ : (X x y : set) → 𝒰 ᵖ)
    X (p : ⋀ x ∈ X , ∃! λ y → ϕ X x y)
    → ----------------------------------------
    ∃ λ Y → ⋀ x ∈ X , ⋁ y ∈ Y , ϕ X x y

  foundation :
    ∀ x (p : ∃ λ y → y ∈ x)
    → -------------------------
    ⋁ y ∈ x , ¬ (∃ λ z → z ∈ x ∧ z ∈ y)

  choice :
    ∀ F (p : ⋀ x ∈ F , x ≠∅ ∧ (⋀ y ∈ F , x == y ∨ disjoint x y))
    → -----------------------------------------------------------
    ∃ λ S → ⋀ x ∈ F , ∃! λ z → z ∈ S ∧ z ∈ x

