{-# OPTIONS --prop --exact-split #-}
module Foundation.FormulaSyntax where

open import Foundation.Axiom as Axiom
  renaming (_∈_ to _mem_)
  using (is-formula; set)
open is-formula

open import Proposition.Identity renaming (_==_ to _eq_)
open import Proposition.Sum using (Σₚ; _,_; elem; prop)
import Logic as L

Formula = Σₚ is-formula

infix 135 _∈_
infix 19 _==_
_∈_ _==_ : (x y : set) → Formula
x ∈ y = x mem y , ∈-formula x y
x == y = (x eq y) , ==-formula x y

infixl 15 _∨_
infixl 17 _∧_
_∧_ _∨_ : (ϕ ψ : Formula) → Formula
(ϕ , p) ∧ (ψ , q) = (ϕ L.∧ ψ) , ∧-formula p q
(ϕ , p) ∨ (ψ , q) = (ϕ L.∨ ψ) , ∨-formula p q

infix 18 ¬_ 
¬_ : (ϕ : Formula) → Formula
¬ (ϕ , p) = (L.¬ ϕ) , ¬-formula p

A_ ∃_ : (ϕ : set → Formula) → Formula
A ϕ = (∀ v → elem (ϕ v)) , ∀-formula (λ v → prop (ϕ v))
∃ ϕ = (L.∃ λ v → elem (ϕ v)) , ∃-formula (λ v → prop (ϕ v))

infix 11 _⟶_ _⟷_
_⟶_ _⟷_ : (ϕ ψ : Formula) → Formula
ϕ ⟶ ψ = ¬ ϕ ∨ ψ
ϕ ⟷ ψ = (ϕ ⟶ ψ) ∧ (ψ ⟶ ϕ)

exists-∈ forall-∈ : (x : set)(ϕ : set → Formula) → Formula
exists-∈ x ϕ = ∃ λ y → y ∈ x ∧ ϕ y
forall-∈ x ϕ = A λ y → y ∈ x ⟶ ϕ y

infixl 11 exists-∈ forall-∈
syntax exists-∈ x (λ y → ϕ) = ⋁ y ∈ x , ϕ
syntax forall-∈ x (λ y → ϕ) = ⋀ y ∈ x , ϕ

infix 135 _∉_ _⊆_
_∉_ _⊆_ disjoint : (x y : set) → Formula
x ∉ y = ¬ x ∈ y
x ⊆ y = ⋀ z ∈ x , z ∈ y
disjoint x y = A λ z → ¬ (z ∈ x ∧ z ∈ y)

_==∅ _≠∅ : (x : set) → Formula
x ==∅ = A λ y → y ∉ x
x ≠∅ = ¬ x ==∅

separation :
  (ϕ : set → Formula) →
  ∀ x →
  L.∃ λ y →
  ∀ u →
  u mem y L.↔ u mem x L.∧ elem (ϕ u)
separation ϕ = Axiom.separation (λ x → elem (ϕ x)) (λ x → prop (ϕ x))

replacement :
  (ϕ : (X x y : set) → Formula) →
  ∀ X (p : Axiom.⋀ x ∈ X , L.∃! λ y → elem (ϕ X x y))
  → ----------------------------------------
  L.∃ λ Y → Axiom.⋀ x ∈ X , Axiom.⋁ y ∈ Y , elem (ϕ X x y)
replacement ϕ =
  Axiom.replacement
    (λ X x y → elem (ϕ X x y)) (λ X x y → prop (ϕ X x y))
