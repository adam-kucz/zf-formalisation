{-# OPTIONS --exact-split #-}
module ZF.Order.Base where

open import ZF.Foundation

module Notation (R : set) where

  _<_ _≮_ _≤_ _≰_ : (x y : set) → Set
  
  x < y = ⟨ x ، y ⟩ ∈ R
  x ≮ y = ¬ x < y
  x ≤ y = x < y ∨ x ≡ y
  x ≰ y = ¬ x ≤ y
