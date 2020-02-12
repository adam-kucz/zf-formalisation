{-# OPTIONS --prop  #-}
module Naive where

open import Foundations.Framework

private
  variable
    A B S S' S'' : Set 𝑙

infix 15 _∉_ _∈_
record NaiveSet (S : Set 𝑚) : Setω where
  infix 15 _∈_
  field
    _∈_ : ∀ {𝑛 𝑙} {A : Set 𝑙} (a : A) (x : S) → Prop 𝑛

open NaiveSet ⦃ ... ⦄ public 

_∈[_]_ : ∀ ⦃ _ : NaiveSet S ⦄ {𝑙} {A : Set 𝑙} (a : A) 𝑛 (x : S) → Prop 𝑛
a ∈[ 𝑛 ] x = _∈_ {𝑛 = 𝑛} a x

_∉_ :
  ⦃ _ : NaiveSet S ⦄
  (a : A)
  (x : S)
  → -------------------
  Prop 𝑛
a ∉ x = ¬ a ∈ x

postulate
  ext :
    ⦃ _ : NaiveSet S ⦄
    ⦃ _ : NaiveSet S' ⦄
    {x : S}
    {y : S'}
    → -------------------------------------
    (∀ (a : A) → a ∈[ 𝑛 ] x ↔ a ∈[ 𝑛 ] y) ↔ x == y

_⊆_ :
  ∀ {𝑛}
  {A : Set 𝑙}
  ⦃ _ : NaiveSet S ⦄
  ⦃ _ : NaiveSet S' ⦄
  (x : S)
  (y : S')
  → -----------------------------
  Prop (𝑙 ⊔ 𝑛)
_⊆_ {𝑛 = 𝑛} {A = A} x y = ∀ (a : A) → a ∈[ 𝑛 ] x → a ∈[ 𝑛 ] y

instance
  Relation⊆ : ⦃ _ : NaiveSet S ⦄ → Relation {A = S} (_⊆_ {𝑛 = 𝑛} {A = A})
  Relation⊆ = record {}
  
  Reflexive⊆ :
    ⦃ _ : NaiveSet S ⦄
    → ----------------------------
    ReflexiveRelation (_⊆_ {𝑛 = 𝑛} {A = A})
  rflx ⦃ Reflexive⊆ ⦄ _ a∈x = a∈x

_⊂_ :
  {A : Set 𝑙}
  {S S' : Set 𝑚}
  ⦃ _ : NaiveSet A S ⦄
  ⦃ _ : NaiveSet A S' ⦄
  (x : S)
  (y : S')
  → ---------------------------
  Prop (𝑙 ⊔ 𝑚 ⊔ 𝑛)
x ⊂ y = x ⊆ y ∧ x ≠ y

-- sym⊆↔== : 
--   ⦃ _ : NaiveSet {𝑛 = 𝑛} A S ⦄
--   {x y : S}
--   → -----------------------------
--   x == y ↔ x ⊆ y ∧ y ⊆ x
-- ⟶ (sym⊆↔== {x = x}) refl = rflx , rflx
-- ⟵ sym⊆↔== (y⊆x , x⊆y) = ⟶ ext (λ a → y⊆x a , x⊆y a )

-- infixl 20 _∪_
-- data Union (S : Set 𝑙) (S' : Set 𝑚) : Set (𝑙 ⊔ 𝑚) where
--   _∪_ : S → S' → Union S S'

-- instance
--   UnionSet :
--     ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S ⦄
--     ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S' ⦄
--     → ----------------------------------
--     NaiveSet {𝑛 = 𝑙₀ ⊔ 𝑙₁} A (Union S S')
--   _∈_ ⦃ UnionSet ⦄ a (x ∪ y) = a ∈ x ∨ a ∈ y

-- comm∪ :
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S ⦄
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S' ⦄
--   {x : S}
--   {y : S'}
--   → ----------------------------------
--   x ∪ y == y ∪ x
-- comm∪ = ⟶ ext (λ _ → ∨comm)

-- assoc∪ :
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S ⦄
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S' ⦄
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₂} A S'' ⦄
--   {x : S}
--   {y : S'}
--   {z : S''}
--   → ----------------------------------
--   x ∪ (y ∪ z) == (x ∪ y) ∪ z
-- assoc∪ = ⟶ ext (λ _ → ∨assoc)

-- infixl 20 _∩_
-- data Intersection (S : Set 𝑙) (S' : Set 𝑚) : Set (𝑙 ⊔ 𝑚) where
--   _∩_ : S → S' → Intersection S S'

-- instance
--   IntersectionSet :
--     ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S ⦄
--     ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S' ⦄
--     → -------------------------------------------
--     NaiveSet {𝑛 = 𝑙₀ ⊔ 𝑙₁} A (Intersection S S')
--   _∈_ ⦃ IntersectionSet ⦄ a (x ∩ y) = a ∈ x ∧ a ∈ y

-- comm∩ :
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S ⦄
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S' ⦄
--   {x : S}
--   {y : S'}
--   → ----------------------------------
--   x ∩ y == y ∩ x
-- comm∩ = ⟶ ext (λ _ → ∧comm)

-- assoc∩ :
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S ⦄
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S' ⦄
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₂} A S'' ⦄
--   {x : S}
--   {y : S'}
--   {z : S''}
--   → ----------------------------------
--   x ∩ (y ∩ z) == (x ∩ y) ∩ z
-- assoc∩ = ⟶ ext (λ _ → ∧assoc)

-- infixl 20 _–_
-- data Difference (S : Set 𝑙) (S' : Set 𝑚) : Set (𝑙 ⊔ 𝑚) where
--   _–_ : S → S' → Difference S S'

-- instance
--   DifferenceSet :
--     ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S ⦄
--     ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S' ⦄
--     → ----------------------------------------
--     NaiveSet {𝑛 = 𝑙₀ ⊔ 𝑙₁} A (Difference S S')
--   _∈_ ⦃ DifferenceSet ⦄ a (x – y) = a ∈ x ∧ a ∉ y

-- data Empty : Set where
--   ∅ : Empty

-- instance
--   EmptySet : NaiveSet {𝑛 = 𝑛} A Empty
--   _∈_ ⦃ EmptySet ⦄ a ∅ = ⊥

-- ∅unique :
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S ⦄
--   {x : S}
--   (∀a,a∉x : ∀ {a : A} → a ∉ x)
--   → -------------------------------
--   x == ∅
-- ∅unique ∀a,a∉x = ⟶ ext (λ _ → ∀a,a∉x , ⊥→any)

-- disjoint :
--   {S : Set 𝑙}
--   {S' : Set 𝑚}
--   {S'' : Set 𝑛}
--   (A : S)
--   (B : S')
--   → ------------
--   Prop (𝑙 ⊔ 𝑚)
-- disjoint A B = A ∩ B == ∅

-- data PredicateSet {𝑙 𝑚} : Set 𝑙 → Set (𝑙 ⊔ lsuc 𝑚) where
--    fromPred : (A : Set 𝑙) (P : A → Prop 𝑚) → PredicateSet A

-- syntax fromPred A (λ x → P) = ｛ x ∶ A ∣ P ｝

-- ｛_｝ : (a : A) → PredicateSet A
-- ｛_｝ {A = A} a = fromPred A (_== a)

-- ｛_&_｝ : (a b : A) → PredicateSet A
-- ｛_&_｝ {A = A} a b = fromPred A (λ x → x == a ∨ x == b)


-- instance
--   PredSet : NaiveSet {𝑛 = 𝑙} A (PredicateSet {𝑚 = 𝑙} A)
--   _∈_ ⦃ PredSet ⦄ a (fromPred _ P) = P a

-- ∪pred :
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₀} A S ⦄
--   ⦃ _ : NaiveSet {𝑛 = 𝑙₁} A S' ⦄
--   {x : S}
--   {y : S'}
--   → ------------------------------
--   x ∪ y == ｛ a ∶ A ∣ a ∈ x ∨ a ∈ y ｝
-- ∪pred = ⟶ ext (λ _ → idₚ , idₚ)

-- ⟨_,_⟩ : (a b : A) → PredicateSet (PredicateSet A)
-- ⟨_,_⟩ a b = ｛ ｛ a ｝ & ｛ a & b ｝ ｝

-- sing== :
--   ∀ {a b : A}
--   → -----------------------------------------
--   ｛ a ｝  == ｛ b ｝ ↔ a == b
-- ⟵ sing== refl = refl
-- ⟶ (sing== {a = a}) sing-a==sing-b =
--   ⟶ (⟵ ext sing-a==sing-b a) refl

-- sing==doub :
--   ∀ {a b c : A}
--   → -----------------------------------------
--   ｛ a ｝  == ｛ b & c ｝ ↔ a == b ∧ a == c
-- ⟶ (sing==doub {a = a} {b} {c}) a==b&c =
--   (← ⟶ (⟵ ext (← a==b&c) b) (refl ∨∅)) ,
--   (← ⟶ (⟵ ext (← a==b&c) c) (∅∨ refl))
-- ⟵ sing==doub (refl , refl) = ⟶ ext λ d → _∨∅ , ∨contract

-- pair== :
--   ∀ {a a' b b' : A}
--   → -----------------------------------------
--   ⟨ a , b ⟩ == ⟨ a' , b' ⟩ ↔ a == a' ∧ b == b'
-- ⟵ pair== (refl , refl) = refl
-- _∧_.left (⟶ (pair== {a = a} {a'} {b} {b'}) ab==a'b') =
--   have ｛ a ｝ == ｛ a ｝ ∨ ｛ a ｝ == ｛ a & b ｝    :from: refl ∨∅
--     ⟶ ｛ a ｝ == ｛ a' ｝ ∨ ｛ a ｝ == ｛ a' & b' ｝
--       :by: ⟶ (⟵ ext ab==a'b' ｛ a ｝)
--     ⟶ a == a' :by: aux-a
--   where aux-a : ｛ a ｝ == ｛ a' ｝ ∨ ｛ a ｝ == ｛ a' & b' ｝ → a == a'
--         aux-a (a==a' ∨∅) = ⟶ (⟵ ext a==a' a) refl
--         aux-a (∅∨ a==a'&b') = _∧_.left (⟶ sing==doub a==a'&b')
-- _∧_.right (⟶ (pair== {a = a} {a'} {b} {b'}) ab==a'b')
--   with ⟶ (⟵ ext ab==a'b' ｛ a & b ｝) (∅∨ refl)
-- _∧_.right (⟶ (pair== {a = a} {a'} {b} {b'}) ab==a'b')
--   | a&b==a' ∨∅ with ⟶ sing==doub (← a&b==a')
-- _∧_.right (⟶ (pair== {a = a} {.a} {.a} {b'}) ab==a'b')
--   | _ | refl , refl with ⟵ (⟵ ext ab==a'b' ｛ a & b' ｝) (∅∨ refl)
-- _∧_.right (⟶ (pair== {a = a} {.a} {.a} {b'}) ab==a'b')
--   | _ | _ | a&b'==a ∨∅ = _∧_.right (⟶ sing==doub (← a&b'==a))
-- _∧_.right (⟶ (pair== {a = a} {.a} {.a} {b'}) ab==a'b')
--   | _ | _ | ∅∨ a&b'==a&a =
--     let a==a&a  = ⟵ (sing==doub {a = a}) (refl , refl)
--         a==a&b' = trans a==a&a (← a&b'==a&a)
--     in _∧_.right (⟶ sing==doub a==a&b')
-- _∧_.right (⟶ (pair== {b = b}) _) | ∅∨ a&b==a'&b'
--   with ⟶ (⟵ ext a&b==a'&b' b) (∅∨ refl)
-- _∧_.right (⟶ pair== _) | _ | ∅∨ b==b' = b==b'
-- _∧_.right (⟶ (pair== {a = a}) _) | ∅∨ a&b==a'&b' | refl ∨∅
--   with ⟶ (⟵ ext a&b==a'&b' a) (refl ∨∅)
-- _∧_.right (⟶ (pair== {a' = a'}) _) | ∅∨ a'&a'==a'&b' | _ | refl ∨∅ =
--     let a'==a'&a'  = ⟵ (sing==doub {a = a'}) (refl , refl)
--         a'==a'&b' = trans a'==a'&a' a'&a'==a'&b'
--     in _∧_.right (⟶ sing==doub a'==a'&b')
-- _∧_.right (⟶ pair== ab==a'b') | _ | _ | ∅∨ refl =
--   ← _∧_.left (⟶ pair== ab==a'b')

-- 𝑃 :
--   ⦃ _ : NaiveSet {𝑛 = 𝑛} A S ⦄
--   (x : S)
--   → ---------------------------
--   PredicateSet S
-- 𝑃 {S = S} x = ｛ y ∶ S ∣ y ⊆ x ｝

-- ⋃ :
--   ⦃ _ : NaiveSet {𝑛 = 𝑛} A S ⦄
--   (x : PredicateSet {𝑚 = 𝑚} S)
--   → ---------------------------
--   PredicateSet A
-- ⋃ {A = A} {S = S} x = ｛ a ∶ A ∣ ∃ y ∶ S , y ∈ x ∧ a ∈ y ｝

-- ⋂ :
--   ⦃ _ : NaiveSet {𝑛 = 𝑛} A S ⦄
--   (x : PredicateSet {𝑚 = 𝑚} S)
--   → ---------------------------
--   PredicateSet A
-- ⋂ {A = A} {S = S} x = ｛ a ∶ A ∣ (∀ (y : S) → y ∈ x → a ∈ y) ｝

-- _×_ :
--   ⦃ _ : NaiveSet {𝑛 = 𝑛} A S ⦄
--   (x y : S)
--   → -------------------------------------------
--   PredicateSet (PredicateSet {𝑚 = 𝑚₀} (PredicateSet {𝑚 = 𝑚₁} S))
-- _×_ {A = A} {S = S} x y = ｛ ab ∶ PredicateSet (PredicateSet S)
--   ∣ ∃ a ∶ A , ∃ b ∶ A , ab == ⟨ a , b ⟩ ∧ a ∈ x ∧ b ∈ y ｝

-- [_]_ :
--   (a : A)
--   (_R_ : A → A → Prop 𝑙)
--   ⦃ _ : EquivalenceRelation _R_ ⦄
--   → -------------------
--   PredicateSet A
-- [_]_ {A = A} a _R_ = ｛ b ∶ A ∣ a R b ｝

-- disjoint-equiv-classes :
--   (R : A → A → Prop 𝑙)
--   ⦃ _ : EquivalenceRelation R ⦄
--   (a b : A)
--   → -------------------
--   ((Rab : R a b) → [ a ] R == [ b ] R) ∧
--   ((¬Rab : ¬ R a b) → disjoint {S'' = S} ([ a ] R) ([ b ] R))
-- _∧_.left (disjoint-equiv-classes R a b) Rab =
--   ⟶ ext λ c → (λ Rac → trans (sym Rab) Rac) , (λ Rbc → trans Rab Rbc)
-- _∧_.right (disjoint-equiv-classes R a b) ¬Rab =
--   ⟶ ext λ c → (λ { (Rac , Rbc) → ¬Rab (trans Rac (sym Rbc)) }) , ⊥→any

-- record Poset
--   (A : Set 𝑙)
--   (S : Set 𝑚)
--   ⦃ _ : NaiveSet {𝑛 = 𝑛} A S ⦄
--   (_≤_ : A → A → Prop 𝑝)
--   ⦃ _ : PartialOrdering _≤_ ⦄
--   : --------------------------
--   Prop
--   where
--   constructor poset

-- minimal-element : {!!}
--   -- ⦃ _ : Poset A S _≤_ ⦄ ?
