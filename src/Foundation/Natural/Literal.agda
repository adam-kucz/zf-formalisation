{-# OPTIONS --exact-split #-}
module Foundation.Natural.Literal where

open import Foundation.Axiom
open import Foundation.Pair

-- synonym to make intention of some types clearer
ℕ : Set
ℕ = set

infixl 25 _⁺
_⁺ : (x : ℕ) → ℕ
x ⁺ = x ∪ ｛ x ｝

open import Data.Sum
open ≡-Reasoning

abstract
  ∈⁺ : ∀{x y} → y ∈ x ⁺ ⇔ (y ∈ x ∨ y ≡ x)
  ∈⁺ {x} = mk⇔ (map₂ (from ∈｛ x ｝) ∘ from ∈∪) (to ∈∪ ∘ map₂ (to ∈｛ x ｝))

open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat public
open import Data.Unit using (⊤)
open Data.Unit using (tt) public

instance
  number : Number set
Number.Constraint number _ = ⊤
fromNat ⦃ number ⦄ 0 = ∅
fromNat ⦃ number ⦄ (suc n) = fromNat ⦃ number ⦄ n ⁺
