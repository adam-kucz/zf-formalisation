{-# OPTIONS --prop --exact-split #-}
module Ordering.Definition where

open import Foundation
open Formula

-- Definition 2.1

is-partially-ordered : (P rel : set) → Formula
is-partially-ordered P rel =
  (⋀ p ∈ P , ¬ p < p) ∧
  (⋀ p ∈ P , ⋀ q ∈ P , ⋀ r ∈ P , p < q ∧ q < r ⟶ p < r)
  where _<_ : (x y : set) → Formula
        x < y = ⟦ x ⸴ y ⟧ ∈ rel

is-linear-ordering : (P rel : set) → Formula
is-linear-ordering P rel =
  is-partially-ordered P rel ∧
  (⋀ p ∈ P , ⋀ q ∈ P , p < q ∨ p == q ∨ q < p)
  where _<_ : (x y : set) → Formula
        x < y = ⟦ x ⸴ y ⟧ ∈ rel

-- Definition 2.2

module Terminology {P rel} (lin : holds (is-partially-ordered P rel))
  where
  _<_ _≮_ _≤_ : (x y : set) → Formula
  x < y = ⟦ x ⸴ y ⟧ ∈ rel
  x ≮ y = ¬ x < y
  x ≤ y = x < y ∨ x == y

  in-subset : (ϕ : (a : set) → Formula)(X a : set) → Formula
  in-subset ϕ X a = X ⊆ P ∧ a ∈ X ∧ ϕ a

  module WithSubset X where
    is-maximal is-minimal is-greatest is-least : (a : set) → Formula
    is-maximal = in-subset (λ a → ⋀ x ∈ X , a ≮ x) X
    is-minimal = in-subset (λ a → ⋀ x ∈ X , x ≮ a) X
    is-greatest = in-subset (λ a → ⋀ x ∈ X , x ≤ a) X
    is-least = in-subset (λ a → ⋀ x ∈ X , a ≤ x) X

    is-upper-bound is-lower-bound : (a : set) → Formula
    is-upper-bound a = X ⊆ P ∧ (⋀ x ∈ X , x ≤ a)
    is-lower-bound a = X ⊆ P ∧ (⋀ x ∈ X , a ≤ x)
  open WithSubset public
  
  module WithSubset' X where
    is-supremum is-infimum : (a : set) → Formula
    is-supremum = is-least upper-bounds
      where upper-bounds : set
            upper-bounds = subset P (is-upper-bound X)
    is-infimum = is-greatest lower-bounds
      where lower-bounds : set
            lower-bounds = subset P (is-lower-bound X)
  open WithSubset' public

  is-order-preserving : ∀ {Q rel'}
    (lin' : holds (is-partially-ordered Q rel'))
    (f : set)
    → ---------
    Formula
  is-order-preserving {Q}{rel'} lin' f = f ∶ P ⟶ Q ∧
    (⋀ x ∈ P , ⋀ y ∈ P , x < y ⟶ value-of f at x <' value-of f at y)
    where infix 19 _<'_
          _<'_ = λ x y → ⟦ x ⸴ y ⟧ ∈ rel'

open Terminology public

is-well-ordering : (P < : set) → Formula
is-well-ordering P < =
  is-linear-ordering P < ∧
  (⋀ X ∈ 𝒫[ P ] , X ≠ ∅ ⟶ ∃ λ y → is-least X y)
