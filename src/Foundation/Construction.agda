{-# OPTIONS --prop --exact-split #-}
module Foundation.Construction where

open import Foundation.Axiom
open import Foundation.FormulaSyntax as F using (Formula)
open import Foundation.Corollary as Cor hiding (∅∈𝒫[x]; x∈𝒫[x])

open import Proposition.Sum
open import Logic

open import Axiom.UniqueChoice

∅ : set
∅ = elem (!choice !∅)
∅-def = ∧left (prop (!choice !∅))

separate :
  (ϕ : set → Formula)
  (p : ∃ λ x → ∀ z → elem (ϕ z) → z ∈ x)
  → ---------------------------------
  set
separate ϕ p = elem (!choice (!separate ϕ p))
separate-def = λ ϕ p → ∧left (prop (!choice (!separate ϕ p)))

replace : 
  (ϕ : (X x y : set) → F.Formula) →
  ∀ X (p : ⋀ x ∈ X , ∃! λ y → elem (ϕ X x y)) → 
  set
replace ϕ X fun-ϕ = elem (!choice (!replace ϕ X fun-ϕ))
replace-def = λ ϕ X fun-ϕ → ∧left (prop (!choice (!replace ϕ X fun-ϕ)))

[_⸴_] : (a b : set) → set
[ a ⸴ b ] = elem (!choice ![ a ⸴ b ])
[_⸴_]-def = λ a b → ∧left (prop (!choice ![ a ⸴ b ]))

open import Operation.Binary
open import Logic.Property
open import Proof

instance
  Commutative-pairing : Commutative [_⸴_]

comm ⦃ Commutative-pairing ⦄ x y =
  set-ext [ x ⸴ y ] [ y ⸴ x ] λ z →
    proof z ∈ [ x ⸴ y ]
      〉 _↔_ 〉 z == x ∨ z == y  :by: [ x ⸴ y ]-def z
      〉 _==_ 〉 z == y ∨ z == x :by: comm (z == x) (z == y)
      〉 _↔_ 〉 z ∈ [ y ⸴ x ]     :by: sym $ [ y ⸴ x ]-def z
    qed

[_] : (x : set) → set
[ x ] = elem (!choice ![ x ])
[_]-def = λ x → ∧left (prop (!choice ![ x ]))

open import PropUniverses hiding (X; Y; Z; W)
open import Relation.Binary.Property hiding (_⊆_)
open import Function.Proof

instance
  Postfix∈[-] : UniversalPostfix [_] _∈_
  Irreflexive∈ : Irreflexive _∈_

  Reflexive⊆ : Reflexive _⊆_
  Transitive⊆ : Transitive _⊆_
  Antisymmetric⊆ : Antisymmetric _⊆_

  Composable∈⊆ : Composable 𝒰₀ _∈_ _⊆_

module Composable⊆ where
  open TransMakeComposable _⊆_ public
module Composable∈ where
  open MakeComposable _∈_ public

UniversalPostfix.postfix Postfix∈[-] x = ⟵ ([ x ]-def x) (refl x)

irrefl ⦃ Irreflexive∈ ⦄ x x∈x
  with foundation [ x ] (x , postfix [_] x)
irrefl ⦃ Irreflexive∈ ⦄ x x∈x
  | z , (z∈[x] , ¬y∈z) with ⟶ ([ x ]-def z) z∈[x]
irrefl ⦃ Irreflexive∈ ⦄ x x∈x
  | x , (_ , ¬y∈[x]) | Id.refl .x = ¬y∈[x] (x , (postfix [_] x , x∈x))

refl ⦃ Reflexive⊆ ⦄ _ _ p = p
trans ⦃ Transitive⊆ ⦄ x⊆y y⊆z w w∈x = y⊆z w (x⊆y w w∈x)
antisym ⦃ Antisymmetric⊆ ⦄ {x}{y} x⊆y y⊆x =
  set-ext x y λ z → x⊆y z , y⊆x z

Composable.rel Composable∈⊆ = _∈_
Composable.compose Composable∈⊆ {x} x∈y y⊆z = y⊆z x x∈y

𝒫[_] : (x : set) → set
𝒫[ x ] = elem (!choice !𝒫[ x ])
𝒫[_]-def = λ x → ∧left (prop (!choice !𝒫[ x ]))

∅∈𝒫[x] : ∀ x → ∅ ∈ 𝒫[ x ]
∅∈𝒫[x] x = Cor.∅∈𝒫[x] ∅-def 𝒫[ x ]-def

instance
  Postfix∈𝒫[-] : UniversalPostfix 𝒫[_] _∈_

UniversalPostfix.postfix Postfix∈𝒫[-] x = Cor.x∈𝒫[x] 𝒫[ x ]-def

open import Proposition.Identity hiding (refl)
open import Proposition.Proof

variable
  a b c d : set
  x y z w : set
  X Y Z W : set

[⸴]-== : [ a ⸴ b ] == [ a ⸴ c ] ↔ b == c
⟶ ([⸴]-== {a}{b}{c}) p with ⟶ ([ a ⸴ c ]-def b) b∈[a,c]
  where b∈[a,c] : b ∈ [ a ⸴ c ]
        b∈[a,c] =
          have b ∈ [ a ⸴ b ] :from: ⟵ ([ a ⸴ b ]-def b) (∨right (refl b))
            ⟶ b ∈ [ a ⸴ c ] :by: Id.coe $ ap (b ∈_) p
⟶ [⸴]-== p | ∨right q = q
⟶ ([⸴]-== {a}{a}{c}) p | ∨left (Id.refl a) =
  have c ∈ [ a ⸴ c ]    :from: ⟵ ([ a ⸴ c ]-def c) (∨right (refl c))
    ⟶ c ∈ [ a ⸴ a ]    :by: Id.coe $ ap (c ∈_) $ sym p
    ⟶ c == a ∨ c == a :by: ⟶ ([ a ⸴ a ]-def c)
    ⟶ c == a           :by: Id.coe $ idemp (c == a)
    ⟶ a == c           :by: sym
⟵ ([⸴]-== {a}) (Id.refl b) = refl [ a ⸴ b ]

[⸴]-≠ : ∀ a b → [ a ⸴ b ] ≠ a
[⸴]-≠ a b p = irrefl a $
  Id.coe (ap (a ∈_) p) (⟵ ([ a ⸴ b ]-def a) (∨left (refl a)))

⟦_⸴_⟧ : (a b : set) → set
⟦ a ⸴ b ⟧ = [ a ⸴ [ a ⸴ b ] ]
⟦_⸴_⟧-def = λ a b → ∧left (prop (!choice ![ a ⸴ [ a ⸴ b ] ]))

⟦⸴⟧-== : 
  ⟦ a ⸴ b ⟧ == ⟦ c ⸴ d ⟧ ↔ a == c ∧ b == d
⟵ ⟦⸴⟧-== (Id.refl a , Id.refl b) = refl ⟦ a ⸴ b ⟧
⟶ (⟦⸴⟧-== {a}{b}{c}{d}) p
  with ⟶ (p' a) (∨left (refl a))
     | ⟶ (p' [ a ⸴ b ]) (∨right (refl [ a ⸴ b ]))
  where p' : (x : set) → (x == a ∨ x == [ a ⸴ b ]) ↔ (x == c ∨ x == [ c ⸴ d ])
        p' x =
          proof x == a ∨ x == [ a ⸴ b ]
            〉 _↔_ 〉 x ∈ ⟦ a ⸴ b ⟧           :by: sym $ ⟦ a ⸴ b ⟧-def x
            〉 _==_ 〉 x ∈ ⟦ c ⸴ d ⟧          :by: ap (x ∈_) p
            〉 _↔_ 〉 x == c ∨ x == [ c ⸴ d ] :by: ⟦ c ⸴ d ⟧-def x
          qed
⟶ (⟦⸴⟧-== {a}{b}{c}{d}) p | ∨left (Id.refl a) | ∨left q =
  ⊥-recursion (a == a ∧ b == d) ([⸴]-≠ a b q)
⟶ ⟦⸴⟧-== p | ∨left (Id.refl a) | ∨right q =
  refl a , ⟶ [⸴]-== q
⟶ (⟦⸴⟧-== {.([ c ⸴ d ])} {b} {c} {d}) p
  | ∨right (Id.refl .([ c ⸴ d ]))
  | ∨left [[c⸴d]⸴b]==c =
  ⊥-recursion ([ c ⸴ d ] == c ∧ b == d) contr
  where contr : ⊥
        contr with foundation ⟦ c ⸴ d ⟧
          (c , ⟵ (⟦ c ⸴ d ⟧-def c) (∨left (refl c)))
        contr | z , (z∈⟦c,d⟧ , min-∈) with ⟶ (⟦ c ⸴ d ⟧-def z) z∈⟦c,d⟧
        contr | c , (_ , min-∈) | ∨left (Id.refl _) =
          min-∈ ([ c ⸴ d ] , (
            ⟵ (⟦ c ⸴ d ⟧-def [ c ⸴ d ]) (∨right (refl [ c ⸴ d ])) , (
            have [ c ⸴ d ] ∈ [ [ c ⸴ d ] ⸴ b ]
              :from: ⟵ ([ [ c ⸴ d ] ⸴ b ]-def [ c ⸴ d ]) (∨left (refl [ c ⸴ d ]))
            ⟶ [ c ⸴ d ] ∈ c :by: Id.coe (ap ([ c ⸴ d ] ∈_) [[c⸴d]⸴b]==c))))
        contr | .([ c ⸴ d ]) , (_ , min-∈) | ∨right (Id.refl _) =
          min-∈ (c , (⟵ (⟦ c ⸴ d ⟧-def c) (∨left (refl c)) ,
                      ⟵ ([ c ⸴ d ]-def c) (∨left (refl c))))
⟶ (⟦⸴⟧-== {.([ c ⸴ d ])} {b} {c} {d}) p
  | ∨right (Id.refl .([ c ⸴ d ]))
  | ∨right [[c,d],b]==[c,d] =
  ⊥-recursion ([ c ⸴ d ] == c ∧ b == d) ([⸴]-≠ [ c ⸴ d ] b [[c,d],b]==[c,d])

infixl 150 _∩_
_∩_ : (x y : set) → set
x ∩ y = separate (λ z → z F.∈ x F.∧ z F.∈ y)
                 (x , λ {z (z∈x , _) → z∈x})
_∩_-def : (x y : set) → ∀ z → z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y
x ∩ y -def = separate-def (λ z → z F.∈ x F.∧ z F.∈ y)
                          (x , λ {z (z∈x , _) → z∈x})

instance
  Idempotent-∩ : Idempotent _∩_
  Commutative-∩ : Commutative _∩_
  Associative-∩ : Associative _∩_

idemp ⦃ Idempotent-∩ ⦄ x = set-ext (x ∩ x) x λ z →
  proof z ∈ x ∩ x
    〉 _↔_ 〉  z ∈ x ∧ z ∈ x :by: (x ∩ x -def) z
    〉 _==_ 〉 z ∈ x          :by: idemp (z ∈ x)
  qed

comm ⦃ Commutative-∩ ⦄ x y = set-ext (x ∩ y) (y ∩ x) λ z →
  proof z ∈ x ∩ y
    〉 _↔_ 〉  z ∈ x ∧ z ∈ y :by: (x ∩ y -def) z
    〉 _==_ 〉 z ∈ y ∧ z ∈ x :by: comm (z ∈ x) (z ∈ y)
    〉 _↔_ 〉  z ∈ y ∩ x      :by: sym $ (y ∩ x -def) z
  qed

open import Axiom.PropositionExtensionality

assoc ⦃ Associative-∩ ⦄ x y z = set-ext (x ∩ (y ∩ z)) (x ∩ y ∩ z) λ w →
  proof w ∈ x ∩ (y ∩ z)
    〉 _↔_ 〉  w ∈ x ∧ w ∈ y ∩ z
      :by: (x ∩ (y ∩ z) -def) w
    〉 _==_ 〉 w ∈ x ∧ (w ∈ y ∧ w ∈ z)
      :by: ap (w ∈ x ∧_) $ prop-ext $ (y ∩ z -def) w
    〉 _==_ 〉 w ∈ x ∧ w ∈ y ∧ w ∈ z
      :by: assoc (w ∈ x) (w ∈ y) (w ∈ z)
    〉 _==_ 〉 w ∈ x ∩ y ∧ w ∈ z
      :by: ap (_∧ w ∈ z) $ prop-ext $ sym $ (x ∩ y -def) w
    〉 _↔_ 〉  w ∈ x ∩ y ∩ z
      :by: sym $ ((x ∩ y) ∩ z -def) w
  qed

infixl 148 _-_
_-_ : (x y : set) → set
x - y = separate (λ z → z F.∈ x F.∧ F.¬ z F.∈ y)
                 (x , λ {z (z∈x , _) → z∈x})
_-_-def : (x y : set) → ∀ z → z ∈ x - y ↔ z ∈ x ∧ ¬ z ∈ y
x - y -def = separate-def (λ z → z F.∈ x F.∧ F.¬ z F.∈ y)
                          (x , λ {z (z∈x , _) → z∈x})

open import Axiom.ExcludedMiddle
open import Axiom.FunctionExtensionality

infixr 175 ⋂_
⋂ : ∀ X (p : x ∈ X) → set
⋂ {x} X x∈X =
  separate (λ z → F.⋀ y ∈ X , z F.∈ y)
           (x , λ _ p → p x x∈X)
⋂-def : ∀ X {x} (p : x ∈ X) → ∀ z → z ∈ ⋂ X p ↔ ∀ x → x ∈ X → z ∈ x
⋂-def X {x} p z =
  separate-def (λ z → F.⋀ y ∈ X , z F.∈ y)
               (x , λ _ q → q x p) z

infixr 175 ⋃_
⋃_ : (X : set) → set
⋃ X = elem (!choice (!⋃ X))
⋃-def = λ X → ∧left (prop (!choice (!⋃ X)))

infixl 149 _∪_
_∪_ : (x y : set) → set
x ∪ y = ⋃ [ x ⸴ y ]
_∪_-def : ∀ x y → ∀ z → z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y
(x ∪ y -def) z =
  proof z ∈ x ∪ y
    〉 _↔_ 〉 (∃ λ w → w ∈ [ x ⸴ y ] ∧ z ∈ w)
      :by: ⋃-def [ x ⸴ y ] z
    〉 _==_ 〉 (∃ λ w → (w == x ∨ w == y) ∧ z ∈ w)
      :by: ap (λ — → ∃ λ w → — w ∧ z ∈ w) $
           fun-ext (λ w → prop-ext $ [ x ⸴ y ]-def w)
    〉 _↔_ 〉 z ∈ x ∨ z ∈ y
      :by: step
  qed
  where step : ∃ (λ w → (w == x ∨ w == y) ∧ z ∈ w) ↔ z ∈ x ∨ z ∈ y
        ⟶ step (x , (∨left (Id.refl x) , z∈x)) = ∨left z∈x 
        ⟶ step (y , (∨right (Id.refl y) , z∈y)) = ∨right z∈y
        ⟵ step (∨left p) = x , (∨left (refl x) , p)
        ⟵ step (∨right q) = y , (∨right (refl y) , q)

instance
  Idempotent-∪ : Idempotent _∪_
  Commutative-∪ : Commutative _∪_
  Associative-∪ : Associative _∪_

Idempotent.idemp Idempotent-∪ x = set-ext (x ∪ x) x λ z →
  proof z ∈ x ∪ x
    〉 _↔_ 〉 z ∈ x ∨ z ∈ x :by: (x ∪ x -def) z
    〉 _==_ 〉 z ∈ x         :by: idemp (z ∈ x)
  qed

comm ⦃ Commutative-∪ ⦄ x y = set-ext (x ∪ y) (y ∪ x) λ z →
  proof z ∈ x ∪ y
    〉 _↔_ 〉  z ∈ x ∨ z ∈ y :by: (x ∪ y -def) z
    〉 _==_ 〉 z ∈ y ∨ z ∈ x :by: comm (z ∈ x) (z ∈ y)
    〉 _↔_ 〉  z ∈ y ∪ x      :by: sym $ (y ∪ x -def) z
  qed

assoc ⦃ Associative-∪ ⦄ x y z = set-ext (x ∪ (y ∪ z)) (x ∪ y ∪ z) λ w →
  proof w ∈ x ∪ (y ∪ z)
    〉 _↔_ 〉  w ∈ x ∨ w ∈ y ∪ z
      :by: (x ∪ (y ∪ z) -def) w
    〉 _==_ 〉 w ∈ x ∨ (w ∈ y ∨ w ∈ z)
      :by: ap (w ∈ x ∨_) $ prop-ext $ (y ∪ z -def) w
    〉 _==_ 〉 w ∈ x ∨ w ∈ y ∨ w ∈ z
      :by: assoc (w ∈ x) (w ∈ y) (w ∈ z)
    〉 _==_ 〉 w ∈ x ∪ y ∨ w ∈ z
      :by: ap (_∨ w ∈ z) $ prop-ext $ sym $ (x ∪ y -def) w
    〉 _↔_ 〉  w ∈ x ∪ y ∪ z
      :by: sym $ ((x ∪ y) ∪ z -def) w
  qed

instance
  Prefix∩ : ∀ {x} → UniversalPrefix (_∩ x) _⊆_
  Postfix∪ : ∀ {x} → UniversalPostfix (_∪ x) _⊆_

UniversalPrefix.prefix (Prefix∩ {z}) x y y∈x∩z =
  ∧left $ ⟶ ((x ∩ z -def) y) y∈x∩z

UniversalPostfix.postfix (Postfix∪ {z}) x y y∈x =
  ⟵ ((x ∪ z -def) y) $ ∨left y∈x

infixl 148 _Δ_
_Δ_ : (x y : set) → set
x Δ y = (x - y) ∪ (y - x)

open import Proposition.BinarySum

pair-∈-𝒫 : ∀ {X Y x y}
  (p : x ∈ X)
  (q : y ∈ Y)
  → ---------------------
  [ x ⸴ y ] ∈ 𝒫[ X ∪ Y ]
pair-∈-𝒫 {X}{Y}{x}{y} p q =
  ⟵ (𝒫[ X ∪ Y ]-def [ x ⸴ y ]) λ z z∈[x,y] →
  ⟵ ((X ∪ Y -def) z) $
  ∨-recursion (λ { (Id.refl .x) → ∨left p})
              (λ { (Id.refl .y) → ∨right q}) $
  ⟶ ([ x ⸴ y ]-def z) z∈[x,y]

ordered-pair-∈-𝒫² : ∀ {X Y x y}
  (p : x ∈ X)
  (q : y ∈ Y)
  → ---------------------
  ⟦ x ⸴ y ⟧ ∈ 𝒫[ X ∪ 𝒫[ X ∪ Y ] ]
ordered-pair-∈-𝒫² {X}{Y}{x}{y} p q =
  pair-∈-𝒫 p (pair-∈-𝒫 p q)

private
  _!×_ : (X Y : set) →
    Cor.set[ u ∶ (∃ λ x → ∃ λ y → u == ⟦ x ⸴ y ⟧ ∧ x ∈ X ∧ y ∈ Y) ]

X !× Y = !separate
  (λ u → F.∃ λ x → F.∃ λ y → u F.== ⟦ x ⸴ y ⟧ F.∧ x F.∈ X F.∧ y F.∈ Y)
  (𝒫[ X ∪ 𝒫[ X ∪ Y ] ] ,
   λ {.(⟦ x' ⸴ y' ⟧) (x' , (y' , (Id.refl _ , x'∈X , y'∈Y))) →
        ordered-pair-∈-𝒫² x'∈X y'∈Y})

infixl 160 _×_
_×_ : (X Y : set) → set
X × Y = elem (!choice (X !× Y))

_×_-def : ∀ X Y →
  ∀ z →
  z ∈ X × Y ↔ ∃ λ x → ∃ λ y → z == ⟦ x ⸴ y ⟧ ∧ x ∈ X ∧ y ∈ Y
⟶ ((X × Y -def) z) p = ⟶ (∧left (prop (!choice (X !× Y))) z) p
⟵ ((X × Y -def) z) (x , (y , (Id.refl _ , x∈X , y∈Y))) =
  ⟵ (∧left (prop (!choice (X !× Y))) ⟦ x ⸴ y ⟧)
    (x , (y , (refl _ , x∈X , y∈Y)))

open import Data.Nat

infixl 170 _^_
_^_ : (X : set)(m : ℕ) → set
X ^ 0 = 𝒫[ ∅ ]
X ^ 1 = X
X ^ (m +2) = X ^ (m +1) × X

is-_[_]-tuple : (m : ℕ)(p : 1 < m)(x : set) → 𝒰₀ ᵖ
is- 1 [ p ]-tuple x with s<s→-<- p
... | ()
is- 2 [ _ ]-tuple x = ∃ λ u → ∃ λ v → x == ⟦ u ⸴ v ⟧
is- m +3 [ _ ]-tuple x = ∃ λ u → ∃ λ v →
  x == ⟦ u ⸴ v ⟧ ∧ is- m +2 [ ap suc z<s ]-tuple u

Rel : (m : ℕ)(p : 1 < m) → 𝒰₀ ˙
Rel m p = Σₚ λ R → ⋀ x ∈ R , is- m [ p ]-tuple x 

RelOn : (m : ℕ)(X : set) → 𝒰₀ ˙
RelOn m X = Σₚ λ R → R ⊆ X ^ m

BinRel : 𝒰₀ ˙
BinRel = Rel 2 (ap suc z<s)

variable
  R : BinRel

dom : (R : BinRel) → set
dom (R , _) =
  separate (λ u → F.∃ λ v → ⟦ u ⸴ v ⟧ F.∈ R ) (⋃ R , p)
  where p : ∀ u (p : ∃ λ v → ⟦ u ⸴ v ⟧ ∈ R) → u ∈ ⋃ R
        p u (v , [u,v]∈R) =
          ⟵ (⋃-def R u)
             (⟦ u ⸴ v ⟧ ,
               ([u,v]∈R ,
                ⟵ ([ u ⸴ [ u ⸴ v ] ]-def u) $ ∨left $ refl u))

ran : (R : BinRel) → set
ran (R , _) =
  separate (λ v → F.∃ λ u → ⟦ u ⸴ v ⟧ F.∈ R ) (⋃ ⋃ R , p)
  where p : ∀ v (p : ∃ λ u → ⟦ u ⸴ v ⟧ ∈ R) → v ∈ ⋃ ⋃ R
        p v (u , [u,v]∈R) =
          ⟵ (⋃-def (⋃ R) v) ([ u ⸴ v ] ,
            (⟵ (⋃-def R [ u ⸴ v ]) (⟦ u ⸴ v ⟧ ,
              ([u,v]∈R ,
               ⟵ ([ u ⸴ [ u ⸴ v ] ]-def [ u ⸴ v ]) $ ∨right $ refl [ u ⸴ v ])) ,
             ⟵ ([ u ⸴ v ]-def v) $ ∨right $ refl v))

field-of : (R : BinRel) → set
field-of R = dom R ∪ ran R

is-function : (f : BinRel) → 𝒰₀ ᵖ
is-function (f , _) = ∀ {x y z}
  (p : ⟦ x ⸴ y ⟧ ∈ f)
  (q : ⟦ x ⸴ z ⟧ ∈ f)
  → --------------------
  y == z

Function = Σₚ λ f → is-function f

-- value-of_at_ : (f : Function)(p : x ∈ dom (elem f)) → set
-- value-of f at p = {!!}
