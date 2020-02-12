module Precedences where

-- Terms (150 - 100)

infix 135 _F==_ _F∈_ _F⊆_ _F==⋃_ _F==｛_｝ _F==｛_,_｝ _F==⦅_,_⦆ _F==_∪_ -- LAST
infix 118 F¬_ -- LAST
infixl 117 _F∧_ -- LAST
infixl 115 _F∨_ -- LAST
infixl 114 _F→_ -- LAST
infixl 114 _F↔_ -- LAST
infixr 113 F∀_,_ -- LAST
infixr 113 F∃_,_ -- LAST

-- Types (60 - 50)

-- Logic formers (40 - 30)

-- Descriptive properties (20)

-- Equalities (19)

-- Logic (18 - 10)

-- Proof (10 - 5)

-- Universes (separate)

