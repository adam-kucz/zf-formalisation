{-# OPTIONS --exact-split #-}
module ZF.Foundation where

open import ZF.Foundation.Axiom public
open import ZF.Foundation.Pair public
open import ZF.Foundation.Relation public
open import ZF.Foundation.Function
  renaming (reify to fun-reify; dereify to fun-dereify) public
open import ZF.Foundation.Natural public
open import ZF.Foundation.RecursiveDefinition public
open import ZF.Foundation.WellFoundedness public
