{-# OPTIONS --exact-split #-}
module ZF.Order.Well where

open import ZF.Order.Total
open import ZF.Foundation

is-well-ordering : (R X : set) → Set
is-well-ordering R X = well-founded R X ∧ is-total-order R X

