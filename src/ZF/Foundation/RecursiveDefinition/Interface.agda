{-# OPTIONS --exact-split #-}
module ZF.Foundation.RecursiveDefinition.Interface where

open import ZF.Foundation.RecursiveDefinition.Base
open import ZF.Foundation.Pair
open import ZF.Foundation.Relation hiding (reify)
open import ZF.Foundation.Function
open import ZF.Foundation.Natural
open import ZF.Foundation.Axiom
open import ZF.Foundation.Axiom.Nonconstructive

module RecDef (ϕ : (x : set) → Set)(ψ : (x y z : set) → Set)
              (!ϕ : ∃! ϕ)(!ψ : ∀ x y → ∃! (ψ x y)) where

  private
    θ = let-rec ϕ ψ
    !θ = !let-rec ϕ ψ !ϕ !ψ

  f : set
  f = reify θ !θ

  open ≡-Reasoning 
  open import Function.Reasoning

  private
    let-rec-f⊆f : ⋀ x ∈ ω , ∀{y} → (θxy : θ x y) → elem θxy [ x ] ≡ f [ x ]
    let-rec-f⊆f {x} x∈ω θxy@(f' , _ , _ , _ , refl) =
      let y , _ , !y = !θ x∈ω in
      begin f' [ x ] ≡⟨ sym $ !y θxy ⟩
            y ≡⟨ !y $ reify-valid θ !θ x∈ω ⟩
            f [ x ] ∎

  abstract
    f-is-fun : is-set-fun f
    f-is-fun = reify-is-fun θ !θ

    f-dom : dom f ≡ ω
    f-dom = reify-dom θ !θ
    
    f[0] : ϕ (f [ 0 ])
    f[0] = let v₀ , ϕv₀ , !v₀ = !ϕ
      in case reify-valid θ !θ ∅∈ω of λ
      { (f' , _ , (_ , _ , _ , f'0 , _) , _ , f0≡f'0) →
           ϕv₀ ∶ ϕ v₀
        |> subst ϕ (begin v₀ ≡⟨ sym $ f'0 v₀ ϕv₀ ⟩
                          f' [ 0 ] ≡⟨ sym f0≡f'0 ⟩
                          f [ 0 ] ∎)}

    f[x⁺] : ⋀ x ∈ ω , ψ x (f [ x ])(f [ x ⁺ ])
    f[x⁺] {x} x∈ω =
      let x⁺∈ω : x ⁺ ∈ ω
          x⁺∈ω = to ∈ω $ inj₂ $ x , x∈ω , refl
          v , ψv , !v = !ψ x (f [ x ])
      in case reify-valid θ !θ x⁺∈ω of λ
      { θ'xy@(f' , fun' , att@(z , _ , dom≡z⁺ , _ , f'⁺) , x⁺∈dom , fx⁺≡f'x⁺) →
         ψv ∶ ψ x (f [ x ]) v
      |> subst (ψ x $ (f [ x ])) (
         let x∈domf' : x ∈ dom f'
             x∈domf' = x∈ω→transitive-x (domf∈ω ϕ ψ !ϕ !ψ θ'xy) x⁺∈dom $
                       to ∈⁺ $ inj₂ refl
             x⁺v∈f' = f'⁺ x∈domf' (f' [ x ]) v
               (λ { refl → x∉x $ subst (x ⁺ ∈_) dom≡z⁺ x⁺∈dom })
               refl (subst (λ y → ψ x (f' [ x ]) (proj₁ (!ψ x y)))
                           (let-rec-f⊆f x∈ω $ f' , fun' , att , x∈domf' , refl)
                           (proj₁ $ prop $ !ψ x (f' [ x ])))
         in begin v ≡⟨ x⁺v∈f' ∶ ⟨ x ⁺ ، v ⟩ ∈ f'
                    |> to (fun' [ x ⁺ ]≡ v) ∶ _ ∧ f' [ x ⁺ ] ≡ v
                    |> sym ∘ proj₂ ⟩
                  f' [ x ⁺ ] ≡⟨ sym fx⁺≡f'x⁺ ⟩
                  f [ x ⁺ ] ∎)}
