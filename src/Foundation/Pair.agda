{-# OPTIONS --exact-split #-}
module Foundation.Pair where

open import Foundation.Axiom.Base
open import Foundation.Axiom.ZF

open import Relation.Nullary
open import Relation.Binary hiding (_⇔_)
open import Data.Empty
open import Data.Sum using ([_,_])

postulate
  _∈?_ : Decidable _∈_

private
  ｛_،_｝-ϕ : (a b : set) → r-prop
  ｛_،_｝-p : (a b : set) →
    ⋀ x ∈ 𝒫 $ 𝒫 ∅ , ∃! λ y → ｛ a ، b ｝-ϕ (𝒫 $ 𝒫 ∅) x y

｛ a ، b ｝-ϕ _ x y = x ≡ ∅ ∧ y ≡ a ∨ x ≢ ∅ ∧ y ≡ b
｛ a ، b ｝-p {x} x∈P2 with p x x∈P2
  where P1 = 𝒫 ∅
        P2 = 𝒫 P1
        p : ∀ x (x∈P2 : x ∈ P2) → x ≡ ∅ ∨ x ≡ P1
        p x x∈P2 with ∅ ∈? x
        ... | yes ∅∈x = inj₂ $ antisym-⊆
          (to (∈𝒫 P1) x∈P2)
          λ z∈P1 → subst (_∈ x) (sym $ ∈𝒫∅ z∈P1) ∅∈x
        ... | no ∅∉x = inj₁ $ antisym-⊆
          (λ z∈x → case ∈𝒫∅ $ to (∈𝒫 P1) x∈P2 z∈x of λ
                   { refl → ⊥-elim $ ∅∉x z∈x})
          (⊥-elim ∘ ∈∅)
... | inj₁ refl = a , inj₁ (refl , refl) ,
  λ { (inj₁ (_ , refl)) → refl
    ; (inj₂ (∅≢∅ , _)) → ⊥-elim $ ∅≢∅ refl }
... | inj₂ refl = b , inj₂ (𝒫[x]≢x , refl) ,
  λ { (inj₁ (𝒫∅≡∅ , refl)) → ⊥-elim $ 𝒫[x]≢x 𝒫∅≡∅
    ; (inj₂ (_ , refl)) → refl}

｛_،_｝ : (a b : set) → set
｛ a ، b ｝ = replacement ｛ a ، b ｝-ϕ (𝒫 $ 𝒫 ∅) ｛ a ، b ｝-p

｛_｝ : (x : set) → set
｛ x ｝ = ｛ x ، x ｝

∈｛_،_｝ : ∀ a b {x} → x ∈ ｛ a ، b ｝ ⇔ (x ≡ a ∨ x ≡ b)
∈｛ a ، b ｝ {x} = mk⇔
  (λ x∈ab → case to def x∈ab of λ
    { (_ , _ , inj₁ (_ , refl)) → inj₁ refl
    ; (_ , _ , inj₂ (_ , refl)) → inj₂ refl})
  λ { (inj₁ refl) → from def (∅ , from (∈𝒫 P1) (∅⊆ P1) , inj₁ (refl , refl))
    ; (inj₂ refl) → from def (P1 , x∈𝒫[ P1 ] , inj₂ (𝒫[x]≢x , refl))}
  where P1 = 𝒫 ∅
        P2 = 𝒫 P1
        def = ∈replacement ｛ a ، b ｝-ϕ P2 ｛ a ، b ｝-p

∈｛_｝ : ∀ a {x} → x ∈ ｛ a ｝ ⇔ x ≡ a
∈｛ a ｝ = mk⇔ (λ x∈a → case to ∈｛ a ، a ｝ x∈a of [ id , id ])
               (from ∈｛ a ، a ｝ ∘ inj₁)

⟨_،_⟩ : (a b : set) → set
⟨ a ، b ⟩ = ｛ ｛ a ｝ ، ｛ a ، b ｝ ｝

π₁ : set → set
π₁ = ⋃ ∘ ⋂

π₂ : set → set
π₂ p = ⋃ ｛ x ∈ ⋃ p ∣ (⋃ p ≢ ⋂ p → x ∉ ⋂ p) ｝

π₁⟨_،_⟩ : (a  b : set) → π₁ ⟨ a ، b ⟩ ≡ a
π₁⟨ a ، b ⟩ = antisym-⊆
  (λ {z} z∈π₁ab → case to (∈⋃ $ ⋂ ab) z∈π₁ab of λ
    { (x , x∈sep , z∈x) →
      case to (∈⋂ ab) x∈sep of λ
      { (_ , ∀y∈ab,x∈y) →
        case to ∈｛ a ｝ $ ∀y∈ab,x∈y $ from ∈ab $ inj₁ refl of λ {refl → z∈x}
        }})
  (λ z∈a → from (∈⋃ $ ⋂ ab) $
    a ,
    (from (∈⋂ ab) $
     from (∈⋃ ab) (｛ a ｝ ,
       from ∈ab (inj₁ refl) ,
       from ∈｛ a ｝ refl) ,
       λ x∈ab → case to ∈｛ ｛ a ｝ ، ｛ a ، b ｝ ｝ x∈ab of λ
         { (inj₁ refl) → from ∈｛ a ｝ refl
         ; (inj₂ refl) → from ∈｛ a ، b ｝ $ inj₁ refl}) ,
    z∈a)
  where ab = ⟨ a ، b ⟩
        ∈ab = ∈｛ ｛ a ｝ ، ｛ a ، b ｝ ｝

π₂⟨_،_⟩[_] : (a b : set)(a≟b : Dec (a ≡ b)) → π₂ ⟨ a ، b ⟩ ≡ b
π₂⟨ a ، b ⟩[ a≟b ] = antisym-⊆
  (λ z∈π₂ab → case to (∈⋃ ｛b｝) z∈π₂ab of λ
    { (x , x∈｛b｝ , z∈x) →  case to ｛b｝ₚ x∈｛b｝ of λ
    { (x∈⋃ab , not-a) → case to (∈⋃ ab) x∈⋃ab of λ
    { (w , w∈ab , x∈w) → case a≟b of λ
    { (yes refl) → case to ∈｛ ｛ a ｝ ｝ w∈ab of λ
      { refl → case to ∈｛ a ｝ x∈w of λ { refl → z∈x } }
    ; (no a≢b) → case to ∈ab w∈ab of λ
      { (inj₁ refl) → case to ∈｛ a ｝ x∈w of λ
        { refl → ⊥-elim $
                 not-a (a≢b→⋃≢⋂ a≢b) $
                 from (∈⋂ ab)
                 (x∈⋃ab , λ {y} y∈ab → case to ∈ab y∈ab of λ
                 { (inj₁ refl) → from ∈｛ x ｝ refl
                 ; (inj₂ refl) → from ∈｛ x ، b ｝ (inj₁ refl)}) }
      ; (inj₂ refl) → case to ∈｛ a ، b ｝ x∈w of λ
        { (inj₁ refl) → ⊥-elim $
                        not-a (a≢b→⋃≢⋂ a≢b) $
                        from (∈⋂ ab)
                        (x∈⋃ab , λ {y} y∈ab → case to ∈ab y∈ab of λ
                        { (inj₁ refl) → from ∈｛ x ｝ refl
                        ; (inj₂ refl) → from ∈｛ x ، b ｝ (inj₁ refl)})  
        ; (inj₂ refl) → z∈x}} }
    }}})
  λ z∈b → from (∈⋃ ｛b｝) $
    b ,
    from ｛b｝ₚ (
      from (∈⋃ ab) (
        ｛ a ، b ｝ ,
        from ∈ab (inj₂ refl) ,
        from ∈｛ a ، b ｝ (inj₂ refl)) ,
      (λ ⋃≢⋂ → ⋃≢⋂ ∘ to a≡b⇔⋃≡⋂ ∘ b∈⋂→a≡b)) ,
    z∈b
  where ab = ⟨ a ، b ⟩
        ∈ab = ∈｛ ｛ a ｝ ، ｛ a ، b ｝ ｝
        ϕ = λ x → ⋃ ab ≢ ⋂ ab → x ∉ ⋂ ab
        ｛b｝ = ｛ b ∈ ⋃ ab ∣ ϕ b ｝
        ｛b｝ₚ = ｛ b ∈ ⋃ ab ∣ ϕ b ｝ₚ
        open import Function.Reasoning
        b∈⋂→a≡b : b ∈ ⋂ ab → a ≡ b
        b∈⋂→a≡b b∈⋂ = b∈⋂ 
          |> proj₂ ∘ to (∈⋂ ab)            ∶ (⋀ y ∈ ab , b ∈ y)
          |> (_|>_ (from ∈ab $ inj₁ refl)) ∶ b ∈ ｛ a ｝
          |> sym ∘ to ∈｛ a ｝             ∶ a ≡ b
        a≡b⇔⋃≡⋂ : a ≡ b ⇔ ⋃ ab ≡ ⋂ ab
        a≡b⇔⋃≡⋂ = mk⇔
          (λ {refl → set-ext (⋃ ab)(⋂ ab) λ z → mk⇔
            (λ z∈⋃ → from (∈⋂ ab) $ z∈⋃ , λ x∈ab →
            case to ∈｛ ｛ a ｝ ｝ x∈ab , to (∈⋃ ab) z∈⋃ of λ
            { (refl , w , w∈ab , z∈w) → case to ∈｛ ｛ a ｝ ｝ w∈ab of λ
            { refl → z∈w }})
            (sep⊆ _ $ ⋃ ab)
            })
          λ ⋃≡⋂ → ｛ a ، b ｝ ,
                  from ∈ab (inj₂ refl) ,
                  from ∈｛ a ، b ｝ (inj₂ refl) ∶ (⋁ x ∈ ab , b ∈ x)
               |> from (∈⋃ ab)                 ∶ b ∈ ⋃ ab
               |> subst (b ∈_) ⋃≡⋂             ∶ b ∈ ⋂ ab
               |> b∈⋂→a≡b                      ∶ a ≡ b
        a≢b→⋃≢⋂ : a ≢ b → ⋃ ab ≢ ⋂ ab
        a≢b→⋃≢⋂ a≢b = a≢b ∘ from a≡b⇔⋃≡⋂

open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

⟨،⟩≡ : ∀{a b a' b'}(a≟b : Dec (a ≡ b))(a'≟b' : Dec (a' ≡ b'))
  → ----------------------------------------------------------
  ⟨ a ، b ⟩ ≡ ⟨ a' ، b' ⟩ ⇔ (a ≡ a' ∧ b ≡ b')
⟨،⟩≡ {a}{b}{a'}{b'} a≟b a'≟b' = mk⇔
  (λ ab≡a'b' → (
    begin a ≡⟨ sym π₁⟨ a ، b ⟩ ⟩
          π₁ ⟨ a ، b ⟩ ≡⟨ cong π₁ ab≡a'b' ⟩
          π₁ ⟨ a' ، b' ⟩ ≡⟨ π₁⟨ a' ، b' ⟩ ⟩
          a'
    ∎) , (
    begin b ≡⟨ sym π₂⟨ a ، b ⟩[ a≟b ] ⟩
          π₂ ⟨ a ، b ⟩ ≡⟨ cong π₂ ab≡a'b' ⟩
          π₂ ⟨ a' ، b' ⟩ ≡⟨ π₂⟨ a' ، b' ⟩[ a'≟b' ] ⟩
          b'
    ∎))
  (λ { (refl , refl) → refl})
  where open ≡-Reasoning
