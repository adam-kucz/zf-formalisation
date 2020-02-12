{-# OPTIONS --exact-split --prop  #-}
module LAST where

open import PropUniverses
open import Proposition.Identity
open import Proposition.Decidable
open import Function
import Logic as L
open import Data.Nat
open import Data.List
open import Data.Collection
  hiding (_⊆_) renaming (_∈_ to _is-mem_; _∉_ to _is-not-mem_)

-- language primitives

data Name : 𝒰₀ ˙ where
  𝑤 : (n : ℕ) → Name

variable w w' w″ : Name

data Variable : 𝒰₀ ˙ where
  𝑣 : (n : ℕ) → Variable

variable v v' v″ : Variable

instance
  DeicdableName== : Decidable (w == w')
  DeicdableVariable== : Decidable (v == v')

DeicdableName== {𝑤 n} {𝑤 m} with decide (n == m)
DeicdableName== | true n==m = true (ap 𝑤 n==m)
DeicdableName== | false ¬n==m = false λ { (refl (𝑤 n)) → ¬n==m (refl n)}

DeicdableVariable== {𝑣 n} {𝑣 m} with decide (n == m)
DeicdableVariable== | true n==m = true (ap 𝑣 n==m)
DeicdableVariable== | false ¬n==m = false λ { (refl (𝑣 n)) → ¬n==m (refl n)}

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

infix 135 _∈_ _≡_
infix 118 ¬_
infixl 117 _∧_
infixl 115 _∨_
infixr 113 A_,_ ∃_,_
data Formula : 𝒰₀ ˙ where
  _∈_ : (x : ident i)(y : ident j) → Formula
  _≡_ : (x : ident i)(y : ident j) → Formula
  _∨_ : (ϕ ψ : Formula) → Formula
  _∧_ : (ϕ ψ : Formula) → Formula
  ¬_ : (ϕ : Formula) → Formula
  A_,_ : (v : Variable)(ϕ : Formula) → Formula
  ∃_,_ : (v : Variable)(ϕ : Formula) → Formula

variable
  ϕ ϕ' ϕ″ ψ ψ' ψ″ θ θ' θ″ : Formula

private
  get-idents : (u : ident i) → List (ident j)

get-idents {name}{name} u = [ u ]
get-idents {name}{var} u = ∅
get-idents {var}{name} u = ∅
get-idents {var}{var} u = [ u ]

free : (ϕ : Formula) → List (ident i)
free (u ∈ u') = get-idents u ++ get-idents u'
free (u ≡ u') = get-idents u ++ get-idents u'
free (ϕ ∧ ψ) = free ϕ ++ free ψ
free (ϕ ∨ ψ) = free ϕ ++ free ψ
free (¬ ϕ) = free ϕ
free {name}(A _ , ϕ) = free ϕ
free  {var}(A v , ϕ) = remove v (free ϕ)
free {name}(∃ _ , ϕ) = free ϕ
free  {var}(∃ v , ϕ) = remove v (free ϕ)

sentence : (ϕ : Formula) → 𝒰₀ ᵖ
sentence ϕ = ∀ (v : Variable) → v is-not-mem free ϕ

infixl 114 _⟷_ _⟶_
_⟶_ _⟷_ : (ϕ ψ : Formula) → Formula
ϕ ⟶ ψ = ¬ ψ ∨ ϕ
ϕ ⟷ ψ = (ψ ⟶ ϕ) ∧ (ϕ ⟶ ψ)

open import Type.Sum hiding (_,_)
open import Data.Nat.Operation
open import Data.Functor
open import Data.Monad
open import Data.List.Functor

new-var : (l : List (Σ λ i → ident i)) → Variable
new-var =
  𝑣 ∘
  freshℕ ∘
  fmap (λ {(𝑣 n) → n}) ∘
  join ∘
  fmap (get-idents {j = var} ∘ pr₂)

infix 135 _⊆_ _≡⋃_ _≡｛_｝ _≡｛_,_｝ _≡⦅_,_⦆ _≡_∪_
_⊆_ : (x : ident i)(y : ident j) → Formula
x ⊆ y = A vₙ , vₙ ∈ x ⟶ vₙ ∈ y
  where vₙ = new-var [ mk-Σ-implicit x ⸴ mk-Σ-implicit y ]

_≡⋃_ : (x : ident i)(y : ident j) → Formula
x ≡⋃ y = A vₙ , vₙ ∈ x ⟷ (∃ vₘ , vₙ ∈ vₘ ∧ vₘ ∈ y)
  where [x,y] = [ mk-Σ-implicit x ⸴ mk-Σ-implicit y ]
        vₙ = new-var [x,y]
        vₘ = new-var (mk-Σ-implicit vₙ ∷ [x,y])

_≡｛_｝ : (x : ident i)(y : ident j) → Formula
x ≡｛ y ｝ = A vₙ , vₙ ∈ x ⟷ vₙ ≡ y
  where vₙ = new-var [ mk-Σ-implicit x ⸴ mk-Σ-implicit y ]

_≡｛_,_｝ : (x : ident i)(y : ident i')(z : ident i″) → Formula
x ≡｛ y , z ｝ = A vₙ , vₙ ∈ x ⟷ vₙ ≡ y ∨ vₙ ≡ z
  where vₙ = new-var [ mk-Σ-implicit x ⸴ mk-Σ-implicit y ⸴ mk-Σ-implicit z ]

_≡⦅_,_⦆ : (x : ident i)(y : ident i')(z : ident i″) → Formula
x ≡⦅ y , z ⦆ = A vₙ , vₙ ∈ x ⟷ vₙ ≡｛ y ｝ ∨ vₙ ≡｛ y , z ｝
  where vₙ = new-var [ mk-Σ-implicit x ⸴ mk-Σ-implicit y ⸴ mk-Σ-implicit z ]

_≡_∪_ : (x : ident i)(y : ident i')(z : ident i″) → Formula
x ≡ y ∪ z = A vₙ , vₙ ∈ x ⟷ vₙ ∈ y ∧ vₙ ∈ z
  where vₙ = new-var [ mk-Σ-implicit x ⸴ mk-Σ-implicit y ⸴ mk-Σ-implicit z ]

