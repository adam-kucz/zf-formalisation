{-# OPTIONS --exact-split --prop  #-}
module LAST where

open import PropUniverses
open import Proposition.Identity
open import Proposition.Decidable
open import Function
open import Data.Nat
open import Data.List hiding (_++_)
open import Data.Collection
  hiding (_⊆_) renaming (_∈_ to _is-mem_; _∉_ to _is-not-mem_)

-- language primitives

data Name : 𝒰₀ ˙ where
  𝑤 : (n : ℕ) → Name

variable w w' w″ : Name

data Variable : 𝒰₀ ˙ where
  𝑣 : (n : ℕ) → Variable

variable v v' v″ : Variable

pattern w₀ = 𝑤 0
pattern w₁ = 𝑤 1
pattern w₂ = 𝑤 2
pattern w₃ = 𝑤 3
pattern v₀ = 𝑣 0
pattern v₁ = 𝑣 1
pattern v₂ = 𝑣 2
pattern v₃ = 𝑣 3

-- auxiliary structure

data Identifier : 𝒰₀ ˙ where
  name var : Identifier

ident : Identifier → 𝒰₀ ˙
ident name = Name
ident var = Variable

module IdentifierVariable where
  variable
    i i' i″ j j' j″ : Identifier
open IdentifierVariable

module VariableVariable where
  variable
    x x' x″ y y' y″ z z' z″ : ident i
open VariableVariable

instance
  DeicdableName== : Decidable (w == w')
  DeicdableVariable== : Decidable (v == v')
  DeicdableIdent== : {x y : ident i} → Decidable (x == y)

DeicdableName== {𝑤 n} {𝑤 m} with decide (n == m)
DeicdableName== | true n==m = true (ap 𝑤 n==m)
DeicdableName== | false ¬n==m = false λ { (refl (𝑤 n)) → ¬n==m (refl n)}

DeicdableVariable== {𝑣 n} {𝑣 m} with decide (n == m)
DeicdableVariable== | true n==m = true (ap 𝑣 n==m)
DeicdableVariable== | false ¬n==m = false λ { (refl (𝑣 n)) → ¬n==m (refl n)}

DeicdableIdent== {name} = DeicdableName==
DeicdableIdent== {var} = DeicdableVariable==

open import Logic
  renaming (⟶ to —>) hiding (_,_)

postulate
  _∈_ : (x : ident i)(y : ident j) → 𝒰₀ ᵖ

variable
  ϕ ϕ' ϕ″ ψ ψ' ψ″ θ θ' θ″ : 𝒰₀ ᵖ

data is-formula : (ϕ : 𝒰₀ ᵖ) → 𝒰₁ ˙

open import Type.Sum hiding (_,_)

Formula = Σ λ ϕ → is-formula ϕ

free : (ϕ : Formula) → List (ident i)

data is-formula where
  ∈-formula  : {x : ident i}{y : ident j} → is-formula (x ∈ y)
  ==-formula : {x : ident i}{y : ident j} → is-formula (x == y)
  ∨-formula :
    (p : is-formula ϕ)
    (q : is-formula ψ)
    → --------------------
    is-formula (ϕ ∨ ψ)
  ∧-formula :
    (p : is-formula ϕ)
    (q : is-formula ψ)
    → --------------------
    is-formula (ϕ ∧ ψ)
  ¬-formula :
    (p : is-formula ϕ)
    → --------------------
    is-formula (¬ ϕ)
  ∀-formula :
    (v : Variable)
    (p : is-formula ϕ)
    → --------------------
    is-formula ϕ
  ∃-formula : {ϕ : Variable → 𝒰₀ ᵖ}
    (p : ∀ v → is-formula (ϕ v))
    → --------------------
    is-formula (∃ λ v → ϕ v)

private
  get-idents : (u : ident i) → List (ident j)

get-idents {name}{name} u = [ u ]
get-idents {name}{var} u = ∅
get-idents {var}{name} u = ∅
get-idents {var}{var} u = [ u ]

open import Data.Collection.Listable.Function

free' : (p : is-formula ϕ) → List (ident i)
free' (∈-formula {x = x}{y}) = get-idents x ++ get-idents y
free' (==-formula {x = x}{y}) = get-idents x ++ get-idents y
free' (∨-formula p p₁) = free' p ++ free' p₁
free' (∧-formula p p₁) = free' p ++ free' p₁
free' (¬-formula p) = free' p
-- hacks, try to make nicer
free' {i = name} (∀-formula v p) = {!!} -- free' (p v₀)
free'  {i = var} (∀-formula v p) = {!!}
  -- if v₀ is-mem free' (p v₁)
  --   then free' (p v₀)
  --   else remove v₀ (free' (p v₀))
free' {i = name} (∃-formula p) = free' (p v₀)
free'  {i = var} (∃-formula p) =
  if v₀ is-mem free' (p v₁)
    then free' (p v₀)
    else remove v₀ (free' (p v₀))

free (ϕ Σ., p) = remove-duplicates (free' p)

sentence : (ϕ : Formula) → 𝒰₀ ᵖ
sentence ϕ = ∀ (v : Variable) → v is-not-mem free ϕ

infix 135 _F∈_ _F==_
_F∈_ _F==_ : (x : ident i)(y : ident j) → Formula
x F∈ y = (x ∈ y) Σ., ∈-formula
x F== y = (x == y) Σ., ==-formula

infix 117 _F∧_
infix 115 _F∨_
_F∨_ _F∧_ : (ϕ ψ : Formula) → Formula
(ϕ Σ., p) F∨ (ψ Σ., q) = (ϕ ∨ ψ) Σ., ∨-formula p q
(ϕ Σ., p) F∧ (ψ Σ., q) = (ϕ ∧ ψ) Σ., ∧-formula p q

infix 118 F¬_
F¬_ : (ϕ : Formula) → Formula
F¬ (ϕ Σ., p) = (¬ ϕ) Σ., ¬-formula p

infix 113 Formula∀ Formula∃ Formula∃!
Formula∀ Formula∃ Formula∃! : (ϕ : Variable → Formula) → Formula

Formula∀ ϕ = {!!} -- (∀ v → pr₁ (ϕ v)) Σ., ∀-formula (λ v → pr₂ (ϕ v))
Formula∃ ϕ = (∃ λ v → pr₁ (ϕ v)) Σ., ∃-formula (λ v → pr₂ (ϕ v))

syntax Formula∀ (λ v → ϕ) = F∀ v , ϕ
syntax Formula∃ (λ v → ϕ) = F∃ v , ϕ

infixl 114 _F↔_ _F→_
_F→_ _F↔_ : (ϕ ψ : Formula) → Formula
ϕ F→ ψ = F¬ ϕ F∨ ψ
ϕ F↔ ψ = (ψ F→ ϕ) F∧ (ϕ F→ ψ)

Formula∃! ϕ = F∃ v , ϕ v F∧ (F∀ w , ϕ w F→ w F== v)
syntax Formula∃! (λ v → ϕ) = F∃! v , ϕ

infix 135 _F⊆_ _F==⋃_ _F==｛_｝ _F==｛_,_｝ _F==⦅_,_⦆ _F==_∪_
_F⊆_ _F==⋃_ _F==｛_｝ : (x : ident i)(y : ident j) → Formula

x F⊆ y = F∀ v , v F∈ x F→ v F∈ y
x F==⋃ y = F∀ vₙ , vₙ F∈ x F↔ (F∃ vₘ , vₙ F∈ vₘ F∧ vₘ F∈ y)
x F==｛ y ｝ = F∀ vₙ , vₙ F∈ x F↔ vₙ F== y

_F==｛_,_｝ _F==⦅_,_⦆ _F==_∪_ : (x : ident i)(y : ident i')(z : ident i″) → Formula

x F==｛ y , z ｝ = F∀ vₙ , vₙ F∈ x F↔ vₙ F== y F∨ vₙ F== z
x F==⦅ y , z ⦆ = F∀ vₙ , vₙ F∈ x F↔ vₙ F==｛ y ｝ F∨ vₙ F==｛ y , z ｝
x F== y ∪ z = F∀ vₙ , vₙ F∈ x F↔ vₙ F∈ y F∧ vₙ F∈ z

infix 135 ｛_｝F∈_ ｛_｝F==_
｛_｝F∈_ ｛_｝F==_ : (x : ident i)(y : ident j) → Formula
｛ x ｝F∈ y = F∃ v , (F∀ w , w F∈ v F↔ w F== x) F∧ v F∈ y
｛ x ｝F== y = F∃ v , (F∀ w , w F∈ v F↔ w F== x) F∧ v F== y
