{-# OPTIONS --exact-split #-}
module Foundation.Pair.Base where

open import Foundation.Axiom
open import Foundation.Axiom.Nonconstructive

open import Relation.Nullary
open import Relation.Binary hiding (_⇔_)
open import Data.Empty
open import Data.Sum using ([_,_])

private
  ｛_،_｝-ϕ : (a b : set) → r-prop
  ｛_،_｝-p : (a b : set) →
    ⋀ x ∈ 𝒫 $ 𝒫 ∅ , ∃! λ y → ｛ a ، b ｝-ϕ x y

｛ a ، b ｝-ϕ x y = x ≡ ∅ ∧ y ≡ a ∨ x ≢ ∅ ∧ y ≡ b

abstract
  ｛ a ، b ｝-p {x} x∈P2 with p x x∈P2
    where P1 = 𝒫 ∅
          P2 = 𝒫 P1
          p : ∀ x (x∈P2 : x ∈ P2) → x ≡ ∅ ∨ x ≡ P1
          p x x∈P2 with is? (∅ ∈ x)
          ... | yes ∅∈x = inj₂ $ antisym-⊆
            (from ∈𝒫 x∈P2)
            λ z∈P1 → subst (_∈ x) (sym $ ∈𝒫∅ z∈P1) ∅∈x
          ... | no ∅∉x = inj₁ $ antisym-⊆
            (λ z∈x → case ∈𝒫∅ $ from ∈𝒫 x∈P2 z∈x of λ
                     { refl → ⊥-elim $ ∅∉x z∈x})
            (⊥-elim ∘ ∈∅)
  ... | inj₁ refl = a , inj₁ (refl , refl) ,
    λ { (inj₁ (_ , refl)) → refl
      ; (inj₂ (∅≢∅ , _)) → ⊥-elim $ ∅≢∅ refl }
  ... | inj₂ refl = b , inj₂ (𝒫[x]≢x , refl) ,
    λ { (inj₁ (𝒫∅≡∅ , refl)) → ⊥-elim $ 𝒫[x]≢x 𝒫∅≡∅
      ; (inj₂ (_ , refl)) → refl}

  ｛_،_｝ : (a b : set) → set
  ｛ a ، b ｝ = replacement ｛ a ، b ｝-ϕ ｛ a ، b ｝-p
  
  ｛_｝ : (x : set) → set
  ｛ x ｝ = ｛ x ، x ｝
  
  ∈｛_،_｝ : ∀ a b {x} → x ∈ ｛ a ، b ｝ ⇔ (x ≡ a ∨ x ≡ b)
  ∈｛ a ، b ｝ {x} = mk⇔
    (λ x∈ab → case from def x∈ab of λ
      { (_ , _ , inj₁ (_ , refl)) → inj₁ refl
      ; (_ , _ , inj₂ (_ , refl)) → inj₂ refl})
    λ { (inj₁ refl) → to def (∅ , to ∈𝒫 (∅⊆ P1) , inj₁ (refl , refl))
      ; (inj₂ refl) → to def (P1 , x∈𝒫[ P1 ] , inj₂ (𝒫[x]≢x , refl))}
    where P1 = 𝒫 ∅
          P2 = 𝒫 P1
          def = ∈replacement ｛ a ، b ｝-ϕ ｛ a ، b ｝-p

  ∈｛_｝ : ∀ a {x} → x ∈ ｛ a ｝ ⇔ x ≡ a
  ∈｛ a ｝ = mk⇔ (λ x∈a → case from ∈｛ a ، a ｝ x∈a of [ id , id ])
                 (to ∈｛ a ، a ｝ ∘ inj₁)

  ⟨_،_⟩ : (a b : set) → set
  ⟨ a ، b ⟩ = ｛ ｛ a ｝ ، ｛ a ، b ｝ ｝

⟨_،_⟩' : (a b : set) → set
⟨ a ، b ⟩' = ⟨ a ، b ⟩

abstract
  abs-op≡ : ∀ a b → ⟨ a ، b ⟩ ≡ ⟨ a ، b ⟩'
  abs-op≡ _ _ = refl

  π₁ : set → set
  π₁ = ⋃ ∘ ⋂

  π₂ : set → set
  π₂ p = ⋃ ｛ x ∈ ⋃ p ∣ (⋃ p ≢ ⋂ p → x ∉ ⋂ p) ｝

  π₁⟨_،_⟩ : (a  b : set) → π₁ ⟨ a ، b ⟩ ≡ a
  π₁⟨ a ، b ⟩ = antisym-⊆
    (λ {z} z∈π₁ab → case from ∈⋃ z∈π₁ab of λ
      { (x , x∈sep , z∈x) →
        case from ∈⋂ x∈sep of λ
        { (_ , ∀y∈ab,x∈y) →
          case from ∈｛ a ｝ $ ∀y∈ab,x∈y $ to ∈ab $ inj₁ refl of λ {refl → z∈x}
          }})
    (λ z∈a → to ∈⋃ $
      a ,
      (to ∈⋂ $
       to ∈⋃ (｛ a ｝ ,
         to ∈ab (inj₁ refl) ,
         to ∈｛ a ｝ refl) ,
         λ x∈ab → case from ∈｛ ｛ a ｝ ، ｛ a ، b ｝ ｝ x∈ab of λ
           { (inj₁ refl) → to ∈｛ a ｝ refl
           ; (inj₂ refl) → to ∈｛ a ، b ｝ $ inj₁ refl}) ,
      z∈a)
    where ab = ⟨ a ، b ⟩
          ∈ab = ∈｛ ｛ a ｝ ، ｛ a ، b ｝ ｝
  
  π₂⟨_،_⟩ : (a b : set) → π₂ ⟨ a ، b ⟩ ≡ b
  π₂⟨ a ، b ⟩ = antisym-⊆
    (λ z∈π₂ab → case from ∈⋃ z∈π₂ab of λ
      { (x , x∈｛b｝ , z∈x) →  case from ∈｛b｝ x∈｛b｝ of λ
      { (x∈⋃ab , not-a) → case from ∈⋃ x∈⋃ab of λ
      { (w , w∈ab , x∈w) → case is? (a ≡ b) of λ
      { (yes refl) → case from ∈｛ ｛ a ｝ ｝ w∈ab of λ
        { refl → case from ∈｛ a ｝ x∈w of λ { refl → z∈x } }
      ; (no a≢b) → case from ∈ab w∈ab of λ
        { (inj₁ refl) → case from ∈｛ a ｝ x∈w of λ
          { refl → ⊥-elim $
                   not-a (a≢b→⋃≢⋂ a≢b) $
                   to ∈⋂
                   (x∈⋃ab , λ {y} y∈ab → case from ∈ab y∈ab of λ
                   { (inj₁ refl) → to ∈｛ x ｝ refl
                   ; (inj₂ refl) → to ∈｛ x ، b ｝ (inj₁ refl)}) }
        ; (inj₂ refl) → case from ∈｛ a ، b ｝ x∈w of λ
          { (inj₁ refl) → ⊥-elim $
                          not-a (a≢b→⋃≢⋂ a≢b) $
                          to ∈⋂
                          (x∈⋃ab , λ {y} y∈ab → case from ∈ab y∈ab of λ
                          { (inj₁ refl) → to ∈｛ x ｝ refl
                          ; (inj₂ refl) → to ∈｛ x ، b ｝ (inj₁ refl)})  
          ; (inj₂ refl) → z∈x}} }
      }}})
    λ z∈b → to ∈⋃ $
      b ,
      to ∈｛b｝ (
        to ∈⋃ (
          ｛ a ، b ｝ ,
          to ∈ab (inj₂ refl) ,
          to ∈｛ a ، b ｝ (inj₂ refl)) ,
        (λ ⋃≢⋂ → ⋃≢⋂ ∘ from a≡b⇔⋃≡⋂ ∘ b∈⋂→a≡b)) ,
      z∈b
    where ab = ⟨ a ، b ⟩
          ∈ab = ∈｛ ｛ a ｝ ، ｛ a ، b ｝ ｝
          ϕ = λ x → ⋃ ab ≢ ⋂ ab → x ∉ ⋂ ab
          ｛b｝ = ｛ b ∈ ⋃ ab ∣ ϕ b ｝
          ∈｛b｝ = ∈｛ b ∈ ⋃ ab ∣ ϕ b ｝
          open import Function.Reasoning
          b∈⋂→a≡b : b ∈ ⋂ ab → a ≡ b
          b∈⋂→a≡b b∈⋂ = b∈⋂ 
            |> proj₂ ∘ from ∈⋂             ∶ (⋀ y ∈ ab , b ∈ y)
            |> (_|>_ (to ∈ab $ inj₁ refl)) ∶ b ∈ ｛ a ｝
            |> sym ∘ from ∈｛ a ｝         ∶ a ≡ b
          a≡b⇔⋃≡⋂ : a ≡ b ⇔ ⋃ ab ≡ ⋂ ab
          a≡b⇔⋃≡⋂ = mk⇔
            (λ {refl → set-ext (⋃ ab)(⋂ ab) λ z → mk⇔
              (λ z∈⋃ → to ∈⋂ $ z∈⋃ , λ x∈ab →
              case from ∈｛ ｛ a ｝ ｝ x∈ab , from ∈⋃ z∈⋃ of λ
              { (refl , w , w∈ab , z∈w) → case from ∈｛ ｛ a ｝ ｝ w∈ab of λ
              { refl → z∈w }})
              (sep⊆ _ $ ⋃ ab)
              })
            λ ⋃≡⋂ → ｛ a ، b ｝ ,
                    to ∈ab (inj₂ refl) ,
                    to ∈｛ a ، b ｝ (inj₂ refl) ∶ (⋁ x ∈ ab , b ∈ x)
                 |> to ∈⋃                      ∶ b ∈ ⋃ ab
                 |> subst (b ∈_) ⋃≡⋂           ∶ b ∈ ⋂ ab
                 |> b∈⋂→a≡b                    ∶ a ≡ b
          a≢b→⋃≢⋂ : a ≢ b → ⋃ ab ≢ ⋂ ab
          a≢b→⋃≢⋂ a≢b = a≢b ∘ to a≡b⇔⋃≡⋂
  
  open import Relation.Binary.PropositionalEquality
  
  ⟨,⟩≡ : ∀{a b a' b'}
    → ----------------------------------------------------------
    ⟨ a ، b ⟩ ≡ ⟨ a' ، b' ⟩ ⇔ (a ≡ a' ∧ b ≡ b')
  ⟨,⟩≡ {a}{b}{a'}{b'} = mk⇔
    (λ ab≡a'b' → (
      begin a ≡⟨ sym π₁⟨ a ، b ⟩ ⟩
            π₁ ⟨ a ، b ⟩ ≡⟨ cong π₁ ab≡a'b' ⟩
            π₁ ⟨ a' ، b' ⟩ ≡⟨ π₁⟨ a' ، b' ⟩ ⟩
            a'
      ∎) , (
      begin b ≡⟨ sym π₂⟨ a ، b ⟩ ⟩
            π₂ ⟨ a ، b ⟩ ≡⟨ cong π₂ ab≡a'b' ⟩
            π₂ ⟨ a' ، b' ⟩ ≡⟨ π₂⟨ a' ، b' ⟩ ⟩
            b'
      ∎))
    (λ { (refl , refl) → refl})
    where open ≡-Reasoning

  ∈⟨,⟩ : ∀{a b x} → x ∈ ⟨ a ، b ⟩ ⇔ (x ≡ ｛ a ｝ ∨ x ≡ ｛ a ، b ｝)
  ∈⟨,⟩ = ∈｛ _ ، _ ｝

infixr 22 _∪_ _-_
infixr 23 _∩_
_∪_ _∩_ _-_ : (A B : set) → set
A ∪ B = ⋃ ｛ A ، B ｝
A ∩ B = ⋂ ｛ A ، B ｝
A - B = ｛ x ∈ A ∣ x ∉ B ｝

private
  variable
    A B : set

abstract
  ∈∪ : ∀{x} → x ∈ A ∪ B ⇔ (x ∈ A ∨ x ∈ B)
  ∈∪ {A}{B} = mk⇔
    (λ x∈A∪B → case from ∈⋃ x∈A∪B of λ
      { (y , y∈｛A,B｝ , x∈y) → case from ∈｛ A ، B ｝ y∈｛A,B｝ of λ
      { (inj₁ refl) → inj₁ x∈y
      ; (inj₂ refl) → inj₂ x∈y} })
    (λ { (inj₁ x∈A) → to ∈⋃ $ A , to ∈｛ A ، B ｝ (inj₁ refl) , x∈A
       ; (inj₂ x∈B) → to ∈⋃ $ B , to ∈｛ A ، B ｝ (inj₂ refl) , x∈B})
  
  ∈∩ : ∀{x} → x ∈ A ∩ B ⇔ (x ∈ A ∧ x ∈ B)
  ∈∩ {A}{B} = mk⇔
    (λ x∈A∩B → case from ∈⋂ x∈A∩B of λ
      { (x∈⋃｛A،B｝ , ∀y∈｛A،B｝,x∈y) →
        ∀y∈｛A،B｝,x∈y (to ∈｛ A ، B ｝ $ inj₁ refl) ,
        ∀y∈｛A،B｝,x∈y (to ∈｛ A ، B ｝ $ inj₂ refl) })
    (λ {(x∈A , x∈B) → to ∈⋂ $
      to ∈∪ (inj₁ x∈A) ,
      λ y∈｛A,B｝ → case from ∈｛ A ، B ｝ y∈｛A,B｝ of λ
      { (inj₁ refl) → x∈A ; (inj₂ refl) → x∈B}})
  
  ∈- : ∀{x} → x ∈ A - B ⇔ (x ∈ A ∧ x ∉ B)
  ∈- {A}{B} = ∈｛ x ∈ A ∣ x ∉ B ｝

  infixl 24 _×_
  _×_ : (A B : set) → set
  A × B = ｛ x ∈ 𝒫 $ 𝒫 $ A ∪ B ∣ ⋁ a ∈ A , ⋁ b ∈ B , x ≡ ⟨ a ، b ⟩ ｝

  ∈× : ∀{x} → x ∈ A × B ⇔ (⋁ a ∈ A , ⋁ b ∈ B , x ≡ ⟨ a ، b ⟩)
  ∈× {A}{B} = mk⇔ (proj₂ ∘ from ∈｛ x ∈ U ∣ ϕ x ｝)
    (λ { (a , a∈A , b , b∈B , refl) →
      to ∈｛ x ∈ U ∣ ϕ x ｝ $
      to ∈𝒫
        (λ x∈⟨a,b⟩ → case from ∈⟨,⟩ x∈⟨a,b⟩ of λ
        { (inj₁ refl) → to ∈𝒫 $ λ x∈｛a｝ →
        case from ∈｛ a ｝ x∈｛a｝ of λ
        { refl → to ∈∪ $ inj₁ a∈A }
        ; (inj₂ refl) → to ∈𝒫 $ λ x∈｛a,b｝ →
        case from ∈｛ a ، b ｝ x∈｛a,b｝ of λ
        { (inj₁ refl) → to ∈∪ $ inj₁ a∈A
        ; (inj₂ refl) → to ∈∪ $ inj₂ b∈B } }) ,
      a , a∈A , b , b∈B , refl})
    where U = 𝒫 $ 𝒫 $ A ∪ B
          ϕ = λ x → ⋁ a ∈ A , ⋁ b ∈ B , x ≡ ⟨ a ، b ⟩
          -- ∈⟨,⟩ = λ {a}{b}{x} → ∈｛ ｛ a ｝ ، ｛ a ، b ｝ ｝ {x}

  ⟨,⟩∈× : ∀{x y} → ⟨ x ، y ⟩ ∈ A × B ⇔ (x ∈ A ∧ y ∈ B)
  ⟨,⟩∈× {A}{B}{x}{y} = mk⇔
    (λ xy∈A×B → case from ∈× xy∈A×B of λ
    { (x' , x'∈A , y' , y'∈B , xy≡x'y') → case from ⟨,⟩≡ xy≡x'y' of λ
    { (refl , refl) → x'∈A , y'∈B}})
    (λ { (x∈A , y∈B) → to ∈× (x , x∈A , y , y∈B , refl)})
