{-# OPTIONS --exact-split #-}
module Foundation.Function.Base where

open import Foundation.Axiom
open import Foundation.Pair
open import Foundation.Product
open import Data.Product

is-set-fun : (f : set) → Set
is-set-fun f =
  (⋀ e ∈ f , ∃₂ λ x y → e ≡ ⟨ x ، y ⟩) ∧
  ∀{x y z} → ⟨ x ، y ⟩ ∈ f → ⟨ x ، z ⟩ ∈ f → y ≡ z  

infixl 22 _[_] _[_]'
_[_] _[_]' : (f u : set) → set
f [ u ]' = π₂ $ ⋃ ｛ x ∈ f ∣ ∃[ v ] (x ≡ ⟨ u ، v ⟩) ｝

abstract
  dom ran : (f : set) → set
  dom f = ｛ u ∈ ⋃ (⋃ f) ∣ ∃[ v ] ⟨ u ، v ⟩ ∈ f ｝

  ran f = ｛ v ∈ ⋃ (⋃ f) ∣ ∃[ u ] ⟨ u ، v ⟩ ∈ f ｝

  f [ u ] = f [ u ]'

  abs-fun≡ : ∀ f u → f [ u ] ≡ f [ u ]'
  abs-fun≡ f u = refl

open import Relation.Binary.PropositionalEquality using (trans)
open ≡-Reasoning
open import Function.Reasoning
open import Data.Empty

abstract
  fun-∅ : is-set-fun ∅
  fun-∅ = ⊥-elim ∘ ∈∅ , ⊥-elim ∘ ∈∅
  
  fun-｛⟨_،_⟩｝ : ∀ u v → is-set-fun ｛ ⟨ u ، v ⟩ ｝
  fun-｛⟨ u ، v ⟩｝ =
    (λ x∈X → case from ∈｛ ⟨ u ، v ⟩ ｝ x∈X of λ
      { refl → u , v , refl}) ,
    λ { {x}{y}{z} xy∈X xz∈X →
      begin y ≡⟨ sym π₂⟨ x ، y ⟩ ⟩
            π₂ ⟨ x ، y ⟩ ≡⟨ cong π₂ $ from ∈｛ ⟨ u ، v ⟩ ｝ xy∈X ⟩
            π₂ ⟨ u ، v ⟩ ≡⟨ cong π₂ $ sym $ from ∈｛ ⟨ u ، v ⟩ ｝ xz∈X ⟩
            π₂ ⟨ x ، z ⟩ ≡⟨ π₂⟨ x ، z ⟩ ⟩
            z ∎}

  ∈dom : ∀{f u} → u ∈ dom f ⇔ ∃ λ v → ⟨ u ، v ⟩ ∈ f
  ∈dom {f}{u} = mk⇔
    (proj₂ ∘ from ∈dom')
    (λ {(v , uv∈f) → to ∈dom' $
      to ∈⋃ (
        ｛ u ｝ ,
        to ∈⋃ (⟨ u ، v ⟩ , uv∈f , to ∈⟨,⟩ (inj₁ refl)) ,
        to ∈｛ u ｝ refl) ,
      v , uv∈f
    })
    where ∈dom' =  ∈｛ u ∈ ⋃ (⋃ f) ∣ ∃[ v ] ⟨ u ، v ⟩ ∈ f ｝

  ∈ran : ∀{f v} → v ∈ ran f ⇔ ∃ λ u → ⟨ u ، v ⟩ ∈ f
  ∈ran {f}{v} = mk⇔
    (proj₂ ∘ from ∈ran')
    (λ {(u , uv∈f) → to ∈ran' $
      to ∈⋃ (
        ｛ u ، v ｝ ,
        to ∈⋃ (⟨ u ، v ⟩ , uv∈f , to ∈⟨,⟩ (inj₂ refl)) ,
        to ∈｛ u ، v ｝ (inj₂ refl)) ,
      u , uv∈f
    })
    where ∈ran' =  ∈｛ v ∈ ⋃ (⋃ f) ∣ ∃[ u ] ⟨ u ، v ⟩ ∈ f ｝

  fun∪ : ∀{f u v} →
    is-set-fun f →
    u ∉ dom f
    → ------------------------------
    is-set-fun (f ∪ ｛ ⟨ u ، v ⟩ ｝)
  proj₁ (fun∪ {_}{u}{v} (valid , uniq) u∉dom) x∈f∪ = case from ∈∪ x∈f∪ of λ
    { (inj₁ x∈f) → valid x∈f
    ; (inj₂ x∈｛uv｝) → u , v , from ∈｛ ⟨ u ، v ⟩ ｝ x∈｛uv｝}
  prop (fun∪ {_}{u}{v} (valid , uniq) u∉dom) {x}{y}{y'} xy∈f∪ xy'∈f∪ =
    case from ∈∪ xy∈f∪ , from ∈∪ xy'∈f∪ of λ
    { (inj₁ xy∈f , inj₁ xy'∈f) → uniq xy∈f xy'∈f
    ; (inj₁ xy∈f , inj₂ xy'∈｛uv｝) → case from ⟨,⟩≡ $ from ∈uv xy'∈｛uv｝ of λ
      { (refl , refl) → ⊥-elim $ u∉dom $ to ∈dom $ y , xy∈f }
    ; (inj₂ xy∈｛uv｝ , inj₁ xy'∈f) → case from ⟨,⟩≡ $ from ∈uv xy∈｛uv｝ of λ
      { (refl , refl) → ⊥-elim $ u∉dom $ to ∈dom $ y' , xy'∈f }
    ; (inj₂ xy∈｛uv｝ , inj₂ xy'∈｛uv｝) →
      case from ⟨,⟩≡ (from ∈uv xy∈｛uv｝) ,
           from ⟨,⟩≡ (from ∈uv xy'∈｛uv｝) of λ
      { ((refl , refl) , _ , refl) → refl }}
    where ∈uv = ∈｛ ⟨ u ، v ⟩ ｝

  dom∅ : dom ∅ ≡ ∅
  dom∅ = antisym-⊆ (⊥-elim ∘ ∈∅ ∘ proj₂ ∘ from ∈dom)
                   (∅⊆ $ dom ∅)

  dom∪ : ∀ f u v → dom (f ∪ ｛ ⟨ u ، v ⟩ ｝) ≡ dom f ∪ ｛ u ｝
  dom∪ f u v = antisym-⊆
    (λ x∈dom[f∪[u]] → case from ∈dom x∈dom[f∪[u]] of λ
      { (v' , uv∈f∪ ) → case from ∈∪ uv∈f∪ of λ
        { (inj₁ uv∈f) → to ∈∪ $ inj₁ $ to ∈dom $ v' , uv∈f
        ; (inj₂ uv∈｛uv｝) →
          case from ⟨,⟩≡ $ from ∈｛ ⟨ u ، v ⟩ ｝ uv∈｛uv｝ of λ
          { (refl , _) → to ∈∪ $ inj₂ $ to ∈｛ u ｝ refl}}})
    (λ x∈dom∪[u] → case from ∈∪ x∈dom∪[u] of λ
      { (inj₁ x∈domf) → case from ∈dom x∈domf of λ
        { (v' , uv∈f) → to ∈dom $ v' , to ∈∪ (inj₁ uv∈f)}
      ; (inj₂ x∈｛u｝) → case from ∈｛ u ｝ x∈｛u｝ of λ
        { refl → to ∈dom $ v , to ∈∪ (inj₂ $ to ∈｛ ⟨ u ، v ⟩ ｝ refl)}})

  dom｛⟨_,_⟩｝ : ∀ u v → dom ｛ ⟨ u ، v ⟩ ｝ ≡ ｛ u ｝
  dom｛⟨ u , v ⟩｝ =
    begin dom ｛ ⟨ u ، v ⟩ ｝ ≡⟨ cong dom $ sym ∅-∪ ⟩
          dom (∅ ∪ ｛ ⟨ u ، v ⟩ ｝) ≡⟨ dom∪ ∅ u v ⟩
          dom ∅ ∪ ｛ u ｝ ≡⟨ cong (_∪ ｛ u ｝) dom∅ ⟩
          ∅ ∪ ｛ u ｝ ≡⟨ ∅-∪ ⟩
          ｛ u ｝
    ∎

  private
    uv∈f→f[u]≡v : ∀{f}(fun : is-set-fun f){u v}
      → --------------------------------------------------
      ⟨ u ، v ⟩ ∈ f → f [ u ] ≡ v
  uv∈f→f[u]≡v {f} fun {u}{v} uv∈f =
      antisym-⊆
          (λ x∈sep → case from ∈sep x∈sep of λ
            { (x∈f , v' , refl) → to ∈｛ ⟨ u ، v ⟩ ｝ $
              cong ⟨ u ،_⟩ $ proj₂ fun x∈f uv∈f })
          (λ x∈｛u,v｝ → case from ∈｛ ⟨ u ، v ⟩ ｝ x∈｛u,v｝ of λ
            { refl → to ∈sep $ uv∈f , v , refl})
        ∶ ｛ x ∈ f ∣ ∃[ v ] (x ≡ ⟨ u ، v ⟩) ｝ ≡ ｛ ⟨ u ، v ⟩ ｝
      |> cong ⋃ ∶ ⋃ ｛ x ∈ f ∣ ∃[ v ] (x ≡ ⟨ u ، v ⟩) ｝ ≡ ⋃ ｛ ⟨ u ، v ⟩ ｝
      |> flip trans (⋃｛ ⟨ u ، v ⟩ ｝)
        ∶ ⋃ ｛ x ∈ f ∣ ∃[ v ] (x ≡ ⟨ u ، v ⟩) ｝ ≡ ⟨ u ، v ⟩
      |> cong π₂ ∶ f [ u ] ≡ π₂ ⟨ u ، v ⟩
      |> flip trans π₂⟨ u ، v ⟩ ∶ f [ u ] ≡ v
    where ∈sep = ∈｛ x ∈ f ∣ ∃[ v ] (x ≡ ⟨ u ، v ⟩) ｝

  _[_∈dom] : ∀{f}(fun : is-set-fun f){u}(u∈dom : u ∈ dom f)
    → -----------------------------------------------------
    ⟨ u ، f [ u ] ⟩ ∈ f
  fun [ u∈dom ∈dom] = case from ∈dom u∈dom of λ
    { (v , uv∈f) → case uv∈f→f[u]≡v fun uv∈f of λ
    { refl → uv∈f }}

  _[_]≡_ :
    ∀{f}(fun : is-set-fun f) u v
    → ----------------------------------------
    (u ∈ dom f ∧ f [ u ] ≡ v) ⇔ ⟨ u ، v ⟩ ∈ f
  _[_]≡_ {f} fun u v = mk⇔
    (λ { (u∈domf , refl) → case from ∈dom u∈domf of λ
      { (v' , uv∈f) → proj₂ fun uv∈f (fun [ u∈domf ∈dom]) ∶ v' ≡ v
        |> flip (subst (λ v → ⟨ u ، v ⟩ ∈ f)) uv∈f ∶ ⟨ u ، v ⟩ ∈ f} })
    λ uv∈f → to ∈dom (v , uv∈f) , uv∈f→f[u]≡v fun uv∈f
    where ∈sep = ∈｛ x ∈ f ∣ ∃[ v ] (x ≡ ⟨ u ، v ⟩) ｝
