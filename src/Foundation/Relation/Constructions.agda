{-# OPTIONS --exact-split #-}
module Foundation.Relation.Constructions where

open import Foundation.Axiom hiding (_∘_; id)
open import Foundation.Pair
open import Foundation.Relation.Base
open import Foundation.Relation.Reification

id : set → set
id X = reify X X _≡_

_∘_ : (P Q : set) → set
P ∘ Q = reify (dom P)(ran Q) λ x y → ∃ λ z → dereify P x z ∧ dereify Q z y

private variable X Y Z P Q : set

abstract
  id-is-rel : is-rel-on (id X) X X
  id-is-rel x∈id = case from ∈reify x∈id of λ
    { (x , x , refl , x∈X , _ , refl) → to ⟨,⟩∈× (x∈X , x∈X)}

  ∘-is-rel : is-rel-on P X Y → is-rel-on Q Y Z → is-rel-on (P ∘ Q) X Z
  ∘-is-rel P⊆X×Y Q⊆X×Y x∈P∘Q = case from ∈reify x∈P∘Q of λ
    { (x , y , refl , x∈domP , y∈ranQ , _) →
      to ⟨,⟩∈× $ dom⊆ P⊆X×Y x∈domP , ran⊆ Q⊆X×Y y∈ranQ}
