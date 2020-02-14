{-# OPTIONS --prop --exact-split #-}
module Foundation.Axiom where

open import PropUniverses
open import Proposition.Identity
open import Logic hiding (_,_; ⟶)

infix 135 _∈_
postulate
  set : 𝒰₀ ˙
  _∈_ : (x y : set) → 𝒰₀ ᵖ

open import Data.Nat

variable
  ϕ ϕ' ϕ″ ψ ψ' ψ″ θ θ' θ″ : 𝒰₀ ᵖ

data is-formula : (ϕ : 𝒰₀ ᵖ) → 𝒰₁ ᵖ where
  ∈-formula  : ∀ x y → is-formula (x ∈ y)
  ==-formula : ∀ (x y : set) → is-formula (x == y)
  ∨-formula :
    (p : is-formula ϕ)
    (q : is-formula ψ)
    → --------------------
    is-formula (ϕ ∨ ψ)
  ∧-formula :
    (p : is-formula ϕ)
    (q : is-formula ψ)
    → --------------------
    is-formula (ϕ ∧ ψ)
  ¬-formula :
    (p : is-formula ϕ)
    → --------------------
    is-formula (¬ ϕ)
  ∀-formula :
    {ϕ : set → 𝒰₀ ᵖ}
    (p : ∀ v → is-formula (ϕ v))
    → --------------------
    is-formula (∀ v → ϕ v)
  ∃-formula :
    {ϕ : set → 𝒰₀ ᵖ}
    (p : ∀ v → is-formula (ϕ v))
    → --------------------
    is-formula (∃ λ v → ϕ v)

infix 11 _⟶_ _⟷_
_⟶_ _⟷_ : (ϕ ψ : 𝒰₀ ᵖ) → 𝒰₀ ᵖ
ϕ ⟶ ψ = ¬ ϕ ∨ ψ
ϕ ⟷ ψ = (ϕ ⟶ ψ) ∧ (ψ ⟶ ϕ)

⟶-formula :
  (p : is-formula ϕ)
  (q : is-formula ψ)
  → ------------------
  is-formula (ϕ ⟶ ψ)
⟶-formula p q = ∨-formula (¬-formula p) q

⟷-formula :
  (p : is-formula ϕ)
  (q : is-formula ψ)
  → ------------------
  is-formula (ϕ ⟷ ψ)
⟷-formula p q = ∧-formula (⟶-formula p q) (⟶-formula q p)

exists-∈ forall-∈ : (x : set)(ϕ : set → 𝒰₀ ᵖ) → 𝒰₀ ᵖ
exists-∈ x ϕ = ∃ λ y → y ∈ x ∧ ϕ y
forall-∈ x ϕ = ∀ y → y ∈ x ⟶ ϕ y

infixl 11 exists-∈ forall-∈
syntax exists-∈ x (λ y → ϕ) = ⋁ y ∈ x , ϕ
syntax forall-∈ x (λ y → ϕ) = ⋀ y ∈ x , ϕ

infix 135 _∉_ _⊆_
_∉_ _⊆_ disjoint : (x y : set) → 𝒰₀ ᵖ
x ∉ y = ¬ x ∈ y
x ⊆ y = ⋀ z ∈ x , z ∈ y
disjoint x y = ∀ z → ¬ (z ∈ x ∧ z ∈ y)

∉-formula : (x y : set) → is-formula (x ∉ y)
∉-formula x y = ¬-formula (∈-formula x y)

⊆-formula : (x y : set) → is-formula (x ⊆ y)
⊆-formula x y = ∀-formula (λ v → ⟶-formula (∈-formula v x) (∈-formula v y))

disjoint-formula : (x y : set) → is-formula (disjoint x y)
disjoint-formula x y = ∀-formula (λ v →
  ¬-formula (∧-formula (∈-formula v x) (∈-formula v y)))

_==∅ _≠∅ : (x : set) → 𝒰₀ ᵖ
x ==∅ = ∀ y → y ∉ x
x ≠∅ = ¬ x ==∅

==∅-formula : (x : set) → is-formula (x ==∅)
==∅-formula x = ∀-formula (λ v → ∉-formula v x)

≠∅-formula : (x : set) → is-formula (x ≠∅)
≠∅-formula x = ¬-formula (==∅-formula x)

postulate
  set-ext :
    ∀ x y
    (p : ∀ z → z ∈ x ↔ z ∈ y)
    → -----------------------
    x == y

  separation :
    (ϕ : set → 𝒰₀ ᵖ)
    (p : ∀ v → is-formula (ϕ v)) →
    ∀ x →
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
    (ϕ : (X x y : set) → 𝒰₀ ᵖ)
    (p : ∀ X x y → is-formula (ϕ X x y)) →
    ∀ X (p : ⋀ x ∈ X , ∃! λ y → ϕ X x y)
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

