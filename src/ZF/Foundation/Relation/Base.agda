{-# OPTIONS --exact-split #-}
module ZF.Foundation.Relation.Base where

open import ZF.Foundation.Axiom
open import ZF.Foundation.Pair

Rel : (X Y : set) → set
Rel X Y = 𝒫 (X × Y)

abstract
  dom ran : (R : set) → set
  dom R = ｛ u ∈ ⋃ (⋃ R) ∣ ∃[ v ] ⟨ u ، v ⟩ ∈ R ｝

  ran R = ｛ v ∈ ⋃ (⋃ R) ∣ ∃[ u ] ⟨ u ، v ⟩ ∈ R ｝

  private variable R X Y u v : set

  ∈dom : u ∈ dom R ⇔ ∃ λ v → ⟨ u ، v ⟩ ∈ R
  ∈dom {u}{R} = mk⇔
    (proj₂ ∘ from ∈dom')
    (λ {(v , uv∈R) → to ∈dom' $
      to ∈⋃ (
        ｛ u ｝ ,
        to ∈⋃ (⟨ u ، v ⟩ , uv∈R , to ∈⟨,⟩ (inj₁ refl)) ,
        to ∈｛ u ｝ refl) ,
      v , uv∈R
    })
    where ∈dom' =  ∈｛ u ∈ ⋃ (⋃ R) ∣ ∃[ v ] ⟨ u ، v ⟩ ∈ R ｝

  dom∅ : dom ∅ ≡ ∅
  dom∅ = antisym-⊆ (⊥-elim ∘ ∈∅ ∘ proj₂ ∘ from ∈dom)
                   (∅⊆ $ dom ∅)

  dom∪ : ∀ R u v → dom (R ∪ ｛ ⟨ u ، v ⟩ ｝) ≡ dom R ∪ ｛ u ｝
  dom∪ R u v = antisym-⊆
    (λ x∈dom[R∪[u]] → case from ∈dom x∈dom[R∪[u]] of λ
      { (v' , uv∈R∪ ) → case from ∈∪ uv∈R∪ of λ
        { (inj₁ uv∈R) → to ∈∪ $ inj₁ $ to ∈dom $ v' , uv∈R
        ; (inj₂ uv∈｛uv｝) →
          case from ⟨,⟩≡ $ from ∈｛ ⟨ u ، v ⟩ ｝ uv∈｛uv｝ of λ
          { (refl , _) → to ∈∪ $ inj₂ $ to ∈｛ u ｝ refl}}})
    (λ x∈dom∪[u] → case from ∈∪ x∈dom∪[u] of λ
      { (inj₁ x∈domR) → case from ∈dom x∈domR of λ
        { (v' , uv∈R) → to ∈dom $ v' , to ∈∪ (inj₁ uv∈R)}
      ; (inj₂ x∈｛u｝) → case from ∈｛ u ｝ x∈｛u｝ of λ
        { refl → to ∈dom $ v , to ∈∪ (inj₂ $ to ∈｛ ⟨ u ، v ⟩ ｝ refl)}})

  open ≡-Reasoning

  dom｛⟨_,_⟩｝ : ∀ u v → dom ｛ ⟨ u ، v ⟩ ｝ ≡ ｛ u ｝
  dom｛⟨ u , v ⟩｝ =
    begin dom ｛ ⟨ u ، v ⟩ ｝ ≡⟨ cong dom $ sym ∅-∪ ⟩
          dom (∅ ∪ ｛ ⟨ u ، v ⟩ ｝) ≡⟨ dom∪ ∅ u v ⟩
          dom ∅ ∪ ｛ u ｝ ≡⟨ cong (_∪ ｛ u ｝) dom∅ ⟩
          ∅ ∪ ｛ u ｝ ≡⟨ ∅-∪ ⟩
          ｛ u ｝
    ∎

  dom⊆ : R ∈ Rel X Y → dom R ⊆ X
  dom⊆ R∈Rel u∈domR = case from ∈dom u∈domR of λ
    { (v , uv∈R) → proj₁ $ from ⟨,⟩∈× $ from ∈𝒫 R∈Rel uv∈R }

  ∈ran : v ∈ ran R ⇔ ∃ λ u → ⟨ u ، v ⟩ ∈ R
  ∈ran {v}{R} = mk⇔
    (proj₂ ∘ from ∈ran')
    (λ {(u , uv∈R) → to ∈ran' $
      to ∈⋃ (
        ｛ u ، v ｝ ,
        to ∈⋃ (⟨ u ، v ⟩ , uv∈R , to ∈⟨,⟩ (inj₂ refl)) ,
        to ∈｛ u ، v ｝ (inj₂ refl)) ,
      u , uv∈R
    })
    where ∈ran' =  ∈｛ v ∈ ⋃ (⋃ R) ∣ ∃[ u ] ⟨ u ، v ⟩ ∈ R ｝

  ran⊆ : R ∈ Rel X Y → ran R ⊆ Y
  ran⊆ R∈Rel v∈ranR = case from ∈ran v∈ranR of λ
    { (u , uv∈R) → proj₂ $ from ⟨,⟩∈× $ from ∈𝒫 R∈Rel uv∈R }

