{-# OPTIONS --exact-split #-}
module ZF.Foundation.Axiom.Base where

open import Level
open import Function
  using (_⇔_; mk⇔; module Equivalence
        ; id; _∘_; _$_; case_of_; flip; _|>_) public
open Equivalence renaming (f to from; g to to) public
open import Relation.Nullary using (¬_) public
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; sym; subst; cong; trans; module ≡-Reasoning) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Sum renaming (_⊎_ to _∨_) using (inj₁; inj₂) public
open import Data.Product as Prod
  renaming (_×_ to _∧_; proj₁ to elem; proj₂ to prop) public
  using (_,_; ∃-syntax; ∃)
open Prod using (proj₁; proj₂) public

private
  variable
    a b l : Level

∃! : {A : Set a}(P : A → Set b) → Set (a ⊔ b)
∃! = Prod.∃! _≡_

infix 21 _∈_ _∉_
postulate
  set : Set
  _∈_ : (x X : set) → Set

_∉_ : (x X : set) → Set
x ∉ X = ¬ (x ∈ X)

infixr 0 ⋀-syntax ⋁-syntax
⋀-syntax ⋁-syntax : ∀{l}(X : set)(P : (x : set) → Set l) → Set l
⋀-syntax X P = ∀{x}(x∈X : x ∈ X) → P x
⋁-syntax X P = ∃[ x ] (x ∈ X ∧ P x)

syntax ⋀-syntax X (λ x → P) = ⋀ x ∈ X , P
syntax ⋁-syntax X (λ x → P) = ⋁ x ∈ X , P

infix 21 _⊆_
_⊆_ : (A B : set) → Set
A ⊆ B = ∀{x}(x∈A : x ∈ A) → x ∈ B

_=S[_] : (y x : set) → Set
y =S[ x ] = ∀ z → z ∈ y ⇔ (z ∈ x ∨ z ≡ x)

empty nonempty inhabited : (X : set) → Set

empty X = ∀{x} → x ∉ X
nonempty = ¬_ ∘ empty

inhabited X = ∃[ x ] x ∈ X

disjoint : (X Y : set) → Set
disjoint X Y = ∀ x → ¬ (x ∈ X ∧ x ∈ Y)

abstract
  inhabited→nonempty : ∀{X} → inhabited X → nonempty X
  inhabited→nonempty (x , x∈X) x∉X = x∉X x∈X
