{-# OPTIONS --prop --exact-split #-}
module Foundation.Corollary where

open import Foundation.Axiom

open import Proposition.Identity
open import Logic

∅-exists : ∃ λ x → ∀ y → y ∉ x
∅-exists with ∞-exists
∅-exists | ∞ , _
  with separation (λ x → x ≠ x) (λ x → ¬-formula (==-formula x x)) ∞
∅-exists | _ | ∅ , p =
  ∅ , λ u u∈∅ → ∧right (⟶ (p u) u∈∅) (refl u)

𝒫-exact :
  ∀ x →
  ∃ λ 𝒫[x] →
  ∀ z → z ⊆ x ↔ z ∈ 𝒫[x]
𝒫-exact x with 𝒫-exists x
𝒫-exact x | 𝒫-superset , _
  with separation (_⊆ x) (λ z → ⊆-formula z x) 𝒫-superset
𝒫-exact x | 𝒫-superset , p | 𝒫[x] , q =
  𝒫[x] , λ z →
    (λ p' → ⟵ (q z) (p z p' , p')) ,
    (λ q' y → ∧right (⟶ (q z) q') y)

import Foundation.FormulaSyntax as F

pair-exact :
  ∀ (a b : set) →
  ∃ λ x → ⋀ y ∈ x , y == a ∨ y == b
pair-exact a b with ∅-exists
pair-exact a b | ∅ , _ with 𝒫-exact ∅
pair-exact a b | _ | 𝒫[∅] , p =
  {!F.replacement (λ X x y → (x F.==∅ F.∧ y F.== a) F.∨ (x F.≠∅ F.∧ y F.== b)) 𝒫[∅]!}
  where p' : forall-∈ 𝒫[∅] (λ x → ∃! λ (y : set) → (x ==∅ ∧ y == a ∨ x ≠∅ ∧ y == b))
        p' x x∈𝒫[∅] = {!⟵ (p x) x∈𝒫[∅]!}
