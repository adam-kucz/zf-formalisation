{-# OPTIONS --prop --exact-split #-}
module Foundation where

module Axiom where
  open import Foundation.Axiom public

open Axiom hiding (
  _==∅; _≠∅; _∈_; _∉_; _⊆_; _⟷_; disjoint; exists-∈; forall-∈;
  replacement; separation
  ) public

module Formula where
  open import Foundation.FormulaSyntax public

open Formula hiding (
  _==∅; _≠∅; _∈_; _∉_; _⊆_; _⟷_; disjoint; exists-∈; forall-∈;
  replacement; separation
  ) public


module Corollary where
  open import Foundation.Corollary public

open Corollary hiding (∅∈𝒫[x]) public

open import Foundation.Construction public

