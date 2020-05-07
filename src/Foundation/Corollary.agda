{-# OPTIONS --prop --exact-split #-}
module Foundation.Corollary where

open import Foundation.Axiom as Axiom

open import PropUniverses
open import Proposition.Identity hiding (refl)
open import Proposition.Sum hiding (_,_)
open import Logic 
open import Proof

!∅ : ∃! λ x → x ==∅
!∅ with ∞-exists
!∅ | ∞ , _
  with separation (λ x → ¬ x == x) ∞
!∅ | _ | ∅ , p =
  ∅ , (∉∅ ,
    λ ∅' ∉∅' → set-ext ∅' ∅ λ y →
      (λ y∈∅' → ⊥-recursion (y ∈ ∅) (∉∅' y y∈∅')) ,
      (λ y∈∅ → ⊥-recursion (y ∈ ∅') (∉∅ y y∈∅)))
  where ∉∅ : ∀ y → y ∉ ∅
        ∉∅ y y∈∅ = ∧right (⟶ (p y) y∈∅) (refl y)

RecPropSet : (𝐴 : (x y : set) → 𝒰 ᵖ) → 𝒰 ᵖ
RecPropSet 𝐴 = ∃! λ x → ∀ z → z ∈ x ↔ 𝐴 x z

PropSet : (𝐴 : set → 𝒰 ᵖ) → 𝒰 ᵖ
PropSet 𝐴 = RecPropSet (λ _ → 𝐴)

syntax PropSet (λ z → 𝑋) = set[ z ∶ 𝑋 ]

import Logic.Proof

prop-set : ∀ x (𝐴 : set → 𝒰 ᵖ)
  (p : ∀ z → z ∈ x ↔ 𝐴 z)
  → --------------------------------
  PropSet 𝐴
prop-set x 𝐴 p = x , (p , λ y p₁ → set-ext y x λ z →
  proof z ∈ y
    〉 _↔_ 〉 𝐴 z   :by: p₁ z
    〉 _↔_ 〉 z ∈ x :by: isym (p z)
  qed)

!separate :
  (ϕ : set → 𝒰 ᵖ)
  (p : ∃ λ x → ∀ z → ϕ z → z ∈ x)
  → ---------------------------------
  set[ z ∶ ϕ z ]
!separate ϕ (x , _) with separation ϕ x
!separate ϕ (x , p) | x' , p' = prop-set x' ϕ ∈x'
  where ∈x' : ∀ z → z ∈ x' ↔ ϕ z
        ⟶ (∈x' z) q = ∧right $ ⟶ (p' z) q
        ⟵ (∈x' z) q = ⟵ (p' z) (p z q , q)

!𝒫[_] : ∀ x → set[ z ∶ z ⊆ x ]
!𝒫[ x ] = !separate (_⊆ x) (𝒫-exists x)

∅∈𝒫[x] : ∀ {x 𝒫[x] ∅}
  (p : ∅ ==∅)
  (q : ∀ z → z ∈ 𝒫[x] ↔ z ⊆ x)
  → ------------------------------
  ∅ ∈ 𝒫[x]
∅∈𝒫[x] {x}{∅ = ∅} p q = ⟵ (q ∅) λ y r → ⊥-recursion (y ∈ x) (p y r)

x∈𝒫[x] : ∀ {x 𝒫[x]}
  (q : ∀ z → z ∈ 𝒫[x] ↔ z ⊆ x)
  → ------------------------------
  x ∈ 𝒫[x]
x∈𝒫[x] {x} p = ⟵ (p x) λ y p → p

!replace : 
  (ϕ : (X x y : set) → 𝒰 ᵖ) →
  ∀ X (p : ∀ x (p' : x ∈ X) → ∃! λ y → ϕ X x y) → 
  set[ y ∶ (∃ λ x → x ∈ X ∧ ϕ X x y) ]
!replace ϕ X fun-ϕ with replacement ϕ X fun-ϕ
!replace ϕ X fun-ϕ | rep-superset , _
  with separation (λ y → ⋁ x ∈ X , ϕ X x y) rep-superset
!replace ϕ X fun-ϕ | rep-superset , p | rep , q =
  prop-set rep (λ y → ∃ λ x → x ∈ X ∧ ϕ X x y) rep-prop
  where rep-prop : ∀ y → y ∈ rep ↔ ∃ λ x → x ∈ X ∧ ϕ X x y
        ⟶ (rep-prop y) y∈rep = ∧right $ ⟶ (q y) y∈rep
        ⟵ (rep-prop y) (x , (x∈X , ϕ[Xxy]))
          with p x x∈X | fun-ϕ x x∈X
        ⟵ (rep-prop y) p₁@(x , (x∈X , ϕ[Xxy]))
          | y' , (y'∈rep-superset , ϕ[Xxy'])
          | y″ , (ϕ[Xxy″] , uniq-y″)  =
          ⟵ (q y) (Id.coe y'-y-equiv y'∈rep-superset , p₁)
          where y'-y-equiv : y' ∈ rep-superset == y ∈ rep-superset
                y'-y-equiv = ap (_∈ rep-superset) (
                  proof y'
                    === y″ :by: uniq-y″ y' ϕ[Xxy']
                    === y  :by: sym $ uniq-y″ y ϕ[Xxy]
                  qed)

-- construction of pairs is fundamentally non-constructive,
-- but we can limit non-constructiveness to emptiness checking
open import Proposition.Decidable

private
  module Classical where
    open import Axiom.ExcludedMiddle

    is-empty : (x : set) → Decidable (x ==∅)
    is-empty x = excluded-middle (x ==∅)
open Classical

![_⸴_] : (a b : set) → set[ y ∶ y == a ∨ y == b ]
![ a ⸴ b ] with !∅
![ a ⸴ b ] | ∅ , _ with !𝒫[ ∅ ]
![ a ⸴ b ] | _ | 𝒫[∅] , _ with !𝒫[ 𝒫[∅] ]
![ a ⸴ b ] | _ | _ | 𝒫²[∅] , p
  with !replace
    (λ X x y → (x ==∅ ∧ y == a) ∨ (x ≠∅ ∧ y == b))
    𝒫²[∅] p'
  where p' :
          ∀ x → x ∈ 𝒫²[∅] →
          ∃! λ (y : set) →
          x ==∅ ∧ y == a ∨ x ≠∅ ∧ y == b
        p' x _ with is-empty x
        p' x _ | true x==∅ =
            a , (∨left (x==∅ , refl a) ,
            λ { y (∨left (_ , y==a)) → y==a
              ; y (∨right (x≠∅ , _)) →
                  ⊥-recursion (y == a) (x≠∅ x==∅)})
        p' x _ | false x≠∅ =
            b , (∨right (x≠∅ , refl b) ,
            λ { y (∨left (x==∅ , _)) → ⊥-recursion (y == b) (x≠∅ x==∅)
              ; y (∨right (_ , y==b)) → y==b})
![ a ⸴ b ]
  | ∅ , (∅-def , _) | 𝟙 , (𝟙-def , _) | 𝟚 , (𝟚-def , _)
  | [a,b] , ([a,b]-def , _) =
  prop-set [a,b]
    (λ y → y == a ∨ y == b)
    (λ y → [a,b]-prop y ,
           λ { (∨left (Id-refl a)) →
                 ⟵ ([a,b]-def a) (∅ , (∅∈𝟚 , ∨left (∅-def , refl a)))
             ; (∨right (Id-refl b)) →
               ⟵ ([a,b]-def b) (𝟙 , (𝟙∈𝟚 , ∨right (𝟙≠∅ , refl b)))})
  where [a,b]-prop : ∀ y (p : y ∈ [a,b]) → y == a ∨ y == b
        [a,b]-prop y y∈[a,b] with ⟶ ([a,b]-def y) y∈[a,b]
        [a,b]-prop y y∈[a,b] | _ , (_ , ∨left (_ , y==a)) = ∨left y==a
        [a,b]-prop y y∈[a,b] | _ , (_ , ∨right (_ , y==b)) = ∨right y==b
        𝟙≠∅ : 𝟙 ≠∅
        𝟙≠∅ p = p ∅ $ ⟵ (𝟙-def ∅) λ _ p → p
        ∅∈𝟚 : ∅ ∈ 𝟚
        ∅∈𝟚 = ∅∈𝒫[x] ∅-def 𝟚-def
        𝟙∈𝟚 : 𝟙 ∈ 𝟚
        𝟙∈𝟚 = x∈𝒫[x] 𝟚-def

open import Operation.Binary
open import Logic.Property

![_] : (a : set) → set[ y ∶ y == a ]
![ a ] with ![ a ⸴ a ]
![ a ] | [a,a] , ([a,a]-def , _) =
  prop-set [a,a]
    (_== a)
    λ z → proof z ∈ [a,a]
            〉 _↔_ 〉  z == a ∨ z == a :by: [a,a]-def z
            〉 _==_ 〉 z == a          :by: idemp (z == a)
          qed

!⋃ : ∀ X → set[ z ∶ ⋁ y ∈ X , z ∈ y ]
!⋃ X with ⋃-exists X
!⋃ X | ⋃-sup , p =
  !separate
    (λ z → ⋁ y ∈ X , z ∈ y)
    (⋃-sup , λ { z (y , (y∈X , z∈y)) → p y y∈X z z∈y})

-- !∞ : RecPropSet λ ∞ z → z ==∅ ∨ (∃ λ y → z =S[ y ] ∧ y ∈ ∞)
-- !∞ with ∞-exists
-- !∞ | ∞ , p = {!separation (λ x → )!}

-- ∃! λ ∞ → ∀ z → z ∈ ∞ ↔ (z ==∅ ∨ (∃ λ y → z =S[ y ] ∧ y ∈ ∞))

-- separation :
--     ∀ (ϕ : set → 𝒰 ᵖ)
--     x →
--     ∃ λ y →
--     ∀ u →
--     u ∈ y ↔ u ∈ x ∧ ϕ u
