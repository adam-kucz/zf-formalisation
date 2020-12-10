{-# OPTIONS --exact-split #-}
module ZF.Order.Total where

open import ZF.Foundation
open import ZF.Order.Base

is-total-order : (R X : set) → Set
is-total-order R X =
  is-rel-on R X X ∧
  (⋀ x ∈ X , x ≮ x) ∧
  (⋀ x ∈ X , ⋀ y ∈ X , ⋀ z ∈ X , (x < y → y < z → x < z)) ∧
  (⋀ x ∈ X , ⋀ y ∈ X , x < y ∨ x ≡ y ∨ y < x)
  where open Notation R

private variable R R' X Y : set

isomorphic : is-total-order R X → is-total-order R' Y → Set
isomorphic {R}{X}{R'}{Y} ordR ordR' = {!!}
