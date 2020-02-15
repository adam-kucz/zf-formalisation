module Precedences where

-- Terms (200 - 100)

infixl 170 _^_ -- Construction
infixr 165 ⋃_ ⋂_ -- Construction
infixl 160 _×_ -- Construction
infixl 150 _∩_ -- Construction
infixl 149 _∪_ -- Construction
infixl 148 _-_ _Δ_ -- Construction
infix 135 _∈_ _∉_ _⊆_ -- Axiom

-- Types (60 - 50)

-- Logic formers (40 - 30)

-- Descriptive properties (20)

-- Equalities (19)

-- Logic (18 - 10)

infixl 11 ∃_∈_,_ ⋀_∈_,_ -- Axiom
infix 11 _⟶_ _⟷_ -- Axiom

-- Proof (10 - 5)

-- Universes (separate)

