{-# OPTIONS --exact-split --safe --without-K  #-}
module SetConstructor where

open import Universes

data set : 𝒰₀ ˙ where
  ∅ : set
  𝒫 : (x : set) → set

variable
   x x' x″ y y' y″ z z' z″ : set

