{-# OPTIONS --exact-split #-}
module ZF.Foundation.Axiom.Choice where

open import ZF.Foundation.Axiom.Base

postulate
  choice :
    ∀ F (p : ⋀ x ∈ F , nonempty x ∧ (⋀ y ∈ F , (x ≡ y ∨ disjoint x y)))
    → -----------------------------------------------------------
    ∃[ S ] (⋀ x ∈ F , ∃! λ z → z ∈ S ∧ z ∈ x)

