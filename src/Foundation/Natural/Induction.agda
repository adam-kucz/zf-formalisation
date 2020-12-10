{-# OPTIONS --exact-split #-}
module Foundation.Natural.Induction where

open import Foundation.Axiom
open import Foundation.Natural.Literal

is-inductive : set → Set
is-inductive A = ∅ ∈ A ∧ (⋀ x ∈ A , x ⁺ ∈ A)

private
  ∞ = elem ∞-exists
  ∈∞ = prop ∞-exists
  Φ = λ n → ∀{A} → is-inductive A → n ∈ A

ω : set
ω = ｛ n ∈ ∞ ∣ Φ n ｝

open import Data.Empty

abstract
  ∅∈∞ : ∅ ∈ ∞
  ∅∈∞ with proj₁ ∈∞
  ... | ∅' , empty-∅' , ∅'∈∞
    with antisym-⊆ (∅⊆ ∅') λ x∈∅' → ⊥-elim $ empty-∅' x∈∅'
  ... | refl = ∅'∈∞

  inductive-∞ : is-inductive ∞
  inductive-∞ =
    ∅∈∞ ,
    λ {x} x∈∞ → prop ∈∞ x∈∞ (x ⁺) λ _ → ∈⁺
  
  ∅∈ω : ∅ ∈ ω
  ∅∈ω = to ∈｛ n ∈ ∞ ∣ Φ n ｝ $ ∅∈∞ , proj₁
  
  inductive-ω : is-inductive ω
  inductive-ω =
    ∅∈ω ,
    λ x∈ω → to ∈ω $ case from ∈ω x∈ω of λ
      { (x∈∞ , Φx) →
        proj₂ inductive-∞ x∈∞ ,
        λ {A} ind-A → proj₂ ind-A {_} $ Φx ind-A }
    where ∈ω = ∈｛ n ∈ ∞ ∣ Φ n ｝
  
open import Foundation.Axiom.Nonconstructive
  
open import Foundation.Pair
open import Data.Sum
open import Relation.Nullary

abstract
  ∈ω : ∀{x} → x ∈ ω ⇔ (x ≡ ∅ ∨ (⋁ y ∈ ω , x ≡ y ⁺))
  ∈ω {x} = mk⇔
    (λ x∈ω → case from ∈all x∈ω of λ
      { (x∈∞ , Φx) → case is? (x ≡ ∅) of λ
        { (yes refl) → inj₁ refl
        ; (no x≢∅) → inj₂ $ by-contradiction λ ¬∃y →
             to ∈- (∅∈ω , x≢∅ ∘ sym ∘ from ∈｛ x ｝) ,
             (λ {z} z∈ω-x → case from ∈- z∈ω-x of λ
               { (z∈ω , z∉｛x｝) → to ∈- $
                 prop inductive-ω z∈ω ,
                 λ z⁺∈｛x｝ → case from ∈｛ x ｝ z⁺∈｛x｝ of λ
                 { refl → ¬∃y $ z , (proj₁ $ from ∈- z∈ω-x) , refl } })
             ∶ is-inductive (ω - ｛ x ｝)
          |> Φx {ω - ｛ x ｝} ∶ x ∈ ω - ｛ x ｝
          |> proj₂ ∘ from ∈- ∶ x ∉ ｛ x ｝
          |> (_$ to ∈｛ x ｝ refl) ∶ ⊥ }})
    (λ { (inj₁ refl) → ∅∈ω
       ; (inj₂ (x , x∈ω , refl)) → case from ∈all x∈ω of λ
         { (x∈∞ , Φx) → to ∈all $
           proj₂ inductive-∞ x∈∞ ,
           λ ind-A → prop ind-A $ Φx ind-A}})
    where open import Function.Reasoning
          all = ｛ n ∈ ∞ ∣ Φ n ｝
          ∈all = ∈｛ n ∈ ∞ ∣ Φ n ｝
  
  ω-induction : (ϕ : set → Set)
    (base : ϕ ∅)(step : ⋀ n ∈ ω , (ϕ n → ϕ (n ⁺)))
    → ------------------------------------------------------
    ⋀ n ∈ ω , ϕ n
  ω-induction ϕ base step {n} =
    proj₂ ∘ from ∈S ∘ subst (n ∈_) (antisym-⊆
      (λ x∈ω → inductive-S |> proj₂ (from ∈｛ n ∈ ∞ ∣ Φ n ｝ x∈ω)  )
      (proj₁ ∘ from ∈S))
    where S = ｛ x ∈ ω ∣ ϕ x ｝
          ∈S = ∈｛ x ∈ ω ∣ ϕ x ｝
          inductive-S : is-inductive S
          inductive-S =
            to ∈S (∅∈ω , base) ,
            λ {x} x∈S → case from ∈S x∈S of λ
            { (x∈ω , ϕx) → to ∈S $
              to ∈ω (inj₂ $ x , x∈ω , refl) ,
              step x∈ω ϕx }
  
  syntax ω-induction (λ n → ϕ) base step =
    ϕ by-induction-on n [base: base ,step: step ]

  x∈ω→∅∈x : ⋀ x ∈ ω , (nonempty x → ∅ ∈ x)
  x∈ω→∅∈x = (nonempty x → ∅ ∈ x)
    by-induction-on x
    [base: (λ nonempty∅ → ⊥-elim $ nonempty∅ ∈∅)
    ,step: (λ {x} x∈ω IH _ → to ∈⁺ $ case is? (nonempty x) of λ
      { (yes nonempty-x) → inj₁ $ IH nonempty-x
      ; (no ¬nonempty-x) →
        inj₂ $ antisym-⊆ (∅⊆ x) $ ⊥-elim ∘ dne ¬nonempty-x } )
    ]  

transitive : (t : set) → Set
transitive t = ⋀ y ∈ t , ⋀ x ∈ y , x ∈ t

abstract
  x∈ω→transitive-x : ⋀ x ∈ ω , transitive x
  x∈ω→transitive-x = transitive x by-induction-on x
    [base: ⊥-elim ∘ ∈∅
    ,step: (λ {x} x∈ω trans-x {y} y∈x⁺ {z} z∈y →
      to ∈⁺ $ inj₁ $ case from ∈⁺ y∈x⁺ of λ
      { (inj₁ y∈x) → trans-x y∈x z∈y
      ; (inj₂ refl) → z∈y})
    ]

  transitive-ω : transitive ω
  transitive-ω = (⋀ x ∈ y , x ∈ ω) by-induction-on y
    [base: ⊥-elim ∘ ∈∅
    ,step: (λ {x} x∈ω IH {z} z∈x⁺ → case from ∈⁺ z∈x⁺ of λ
      { (inj₁ z∈x) → IH z∈x
      ; (inj₂ refl) → x∈ω})
    ]
