{-# OPTIONS --exact-split --prop  #-}
module FreeVariables where

open import PropUniverses
open import Type.Sum
open import Proposition.Decidable
open import Data.Collection
open import Data.Collection.Listable.Function
open import Data.List hiding (_++_)
open import Logic
open import Proof

open import LAST hiding (_∈_)
open IdentifierVariable

∈free-param : ∀
  (ϕ : Variable → Formula)
  {v v' : Variable}
  (p : v ≠ v')
  → ----------------------------
  v ∈ free (ϕ v') ↔ ∀ v″ → v ∈ free (ϕ v″)
⟶ (∈free-param ϕ p) p₁ v″ = {!!}
⟵ (∈free-param ϕ p) q = {!!}

∈freeF∀ :
  (ϕ : Variable → Formula)
  → -----------------------------------------------------------
  v ∈ free (Formula∀ ϕ) ↔ ∀ v' → v ∈ free (ϕ v')
⟶ (∈freeF∀ ϕ) p v' with ⟶ ∈remove-duplicates p
⟶ (∈freeF∀ ϕ) p v' | p'
  with decide (v₀ ∈ free' (pr₂ (ϕ v₁)))
       ⦃ ListDecidable∈ ⦃ DeicdableVariable== ⦄ ⦄
⟶ (∈freeF∀ ϕ) p v' | p' | true q = {!!}
⟶ (∈freeF∀ ϕ) p v' | p' | false ¬q = {!!}
⟵ (∈freeF∀ ϕ) q = {!!}

