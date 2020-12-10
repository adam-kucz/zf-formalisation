{-# OPTIONS --exact-split #-}
module Foundation.Relation where

open import Foundation.Axiom
open import Foundation.Pair
open import Foundation.Product

is-rel-on : (R X Y : set) → Set
is-rel-on R X Y = R ⊆ X × Y
