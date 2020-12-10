{-# OPTIONS --exact-split #-}
module ZF.Foundation.RecursiveDefinition.Base where

open import ZF.Foundation.Axiom
open import ZF.Foundation.Function
open import ZF.Foundation.Relation
open import ZF.Foundation.Natural.Induction
open import ZF.Foundation.Natural.Literal

module _ (ϕ : (x : set) → Set)(ψ : (x y z : set) → Set) where
  private
    attempt : (f : set) → Set

  open import ZF.Foundation.Pair
  attempt f = ⋁ x ∈ ω ,
    dom f ≡ x ⁺ ∧
    (∀ y → ϕ y → f [ 0 ] ≡ y ) ∧
    (⋀ u ∈ dom f , ∀ y z →
       u ≢ x →
       f [ u ] ≡ y →
       ψ u y z
       → ------------------------------
       ⟨ u ⁺ ، z ⟩ ∈ f)
  
  let-rec : (x y : set) → Set
  let-rec x y = ∃ λ f → is-set-fun f ∧ attempt f ∧ x ∈ dom f ∧ y ≡ f [ x ]
  
  private
    θ = let-rec
  
  open import ZF.Foundation.Axiom.Nonconstructive
  open import Relation.Nullary

  module _ (!ϕ : ∃! ϕ)(!ψ : ∀ x y → ∃! (ψ x y)) where
    private
      v₀ = elem !ϕ
      pv₀ = proj₁ $ prop !ϕ
      !v₀ = proj₂ $ prop !ϕ
      next = λ f x → elem $ !ψ x (f [ x ])
      pnext = λ f x → proj₁ $ prop $ !ψ x (f [ x ])
      !next = λ f x {y} → proj₂ (prop $ !ψ x (f [ x ])) {y}

      variable x y z f : set

    open ≡-Reasoning
    open import Function.Reasoning
    open import Data.Sum
    import Data.Product as Prod
    abstract
      private
        ⁺∈ : ⋀ y ∈ ω , (x ⁺ ∈ y → x ∈ y)
        ∅∈⁺ : ⋀ x ∈ ω , ∅ ∈ x ⁺
        θ⁻ : ⋀ x ∈ ω , ((p : θ (x ⁺) y) → θ x (elem p [ x ]))

      ⁺∈ y∈ω x⁺∈y = x∈ω→transitive-x y∈ω x⁺∈y $ to ∈⁺ $ inj₂ refl
      ∅∈⁺ = ∅ ∈ x ⁺ by-induction-on x
        [base: to ∈⁺ (inj₂ refl)
        ,step: (λ _ → to ∈⁺ ∘ inj₁) ]       

      domf∈ω : (p : θ x y) → dom (elem p) ∈ ω
      domf∈ω (_ , _ , (z , z∈ω , dom≡z⁺ , _ , _) , _ , refl) =
        subst (_∈ ω) (sym dom≡z⁺) $ to ∈ω $ inj₂ $ z , z∈ω , refl

      θ⁻ {x = x} x∈ω θ@(f , fun , att , x⁺∈dom , refl) =
        f , fun , att , ⁺∈ (domf∈ω θ) x⁺∈dom , refl

      let-rec-agree : ⋀ x ∈ ω , (∀{y y'} → θ x y → θ x y' → y ≡ y')
      let-rec-agree = (∀{y y'} → θ x y → θ x y' → y ≡ y')
        by-induction-on x
        [base: (λ { (f , _ , (_ , _ , _ , f0 , _) , _ , refl)
                    (f' , _ , (_ , _ , _ , f'0 , _) , _ , refl) →
                    begin f [ ∅ ] ≡⟨ f0 v₀ pv₀ ⟩
                          v₀ ≡⟨ sym $ f'0 v₀ pv₀ ⟩
                          f' [ ∅ ] ∎})
        ,step: (λ { {x} x∈ω IH
         θxy@(f , fun , (y , y∈ω , dom≡y⁺ , _ , f⁺) , x⁺∈dom , refl)
          θxy'@(f' , fun' ,
                (y' , y'∈ω , dom'≡y'⁺ , _ , f'⁺) ,
                x⁺∈dom' , refl) →
          begin f [ x ⁺ ] ≡⟨ proj₂ ∘ to (fun [ x ⁺ ]≡ next f x) $
                             f⁺ (⁺∈ (domf∈ω θxy) x⁺∈dom)
                                (f [ x ]) (next f x)
                                (λ {refl → x∉x $ subst (x ⁺ ∈_) dom≡y⁺ x⁺∈dom})
                                refl (pnext f x) ⟩
                next f x ≡⟨ !next f x $
                  subst (λ y → ψ x y $ next f' x)
                        (IH (θ⁻ x∈ω θxy')(θ⁻ x∈ω θxy)) $
                  pnext f' x ⟩
                next f' x ≡⟨
                  sym $ proj₂ ∘ to (fun' [ x ⁺ ]≡ next f' x) $
                  f'⁺ (⁺∈ (domf∈ω θxy') x⁺∈dom')
                      (f' [ x ]) (next f' x)
                      (λ {refl → x∉x $ subst (x ⁺ ∈_) dom'≡y'⁺ x⁺∈dom'})
                      refl (pnext f' x) ⟩
                f' [ x ⁺ ] ∎})]

      private
        extend-dom :
          ⋀ x ∈ ω , ((p : attempt f) → x ∈ dom f → x ⁺ ∉ dom f → elem p ≡ x)
      extend-dom {f}{x} x∈ω (z , z∈ω , dom≡z⁺ , f0 , f⁺) x∈dom x⁺∉dom =
        by-contradiction λ z≢x → x⁺∉dom $
          f⁺ x∈dom (f [ x ]) (next f x) (z≢x ∘ sym) refl (pnext f x)
          ∶ ⟨ x ⁺ ، next f x ⟩ ∈ f
        |> to ∈dom ∘ (next f x ,_) ∶ x ⁺ ∈ dom f

      !let-rec : ⋀ x ∈ ω , ∃! (let-rec x)
      !let-rec = ∃! (θ x) by-induction-on x
        [base: v₀ , θ∅v₀ , let-rec-agree ∅∈ω θ∅v₀
        ,step: (λ { {x} x∈ω
          (.(f [ x ]) ,
            θxy@(f , fun , fp@(z , z∈ω , dom≡z⁺ , f0 , f⁺) , x∈dom , refl) ,
           !y) →
          let x⁺∈ω = to ∈ω $ inj₂ $ x , x∈ω , refl
          in case is? (x ⁺ ∈ dom f) of λ
          { (yes x⁺∈dom) →
            let θx⁺y = f , fun , fp , x⁺∈dom , refl in
            f [ x ⁺ ] , θx⁺y , λ {_} → let-rec-agree x⁺∈ω θx⁺y
          ; (no x⁺∉dom) →
            case extend-dom x∈ω fp x∈dom x⁺∉dom of λ { refl → 
            let f' = f ∪ ｛ ⟨ x ⁺ ، next f x ⟩ ｝
                fun' = fun∪ fun x⁺∉dom
                new∈∪ : ⟨ x ⁺ ، next f x ⟩ ∈ f ∪ ｛ ⟨ x ⁺ ، next f x ⟩ ｝
                new∈∪ = to ∈∪ $ inj₂ $ to ∈｛ _ ｝ refl
                x⁺∈domf' , f'[x⁺]≡next =
                  to (fun∪ fun x⁺∉dom [ x ⁺ ]≡ next f x) new∈∪
                θx⁺next : θ (x ⁺) (next f x)
                θx⁺next =
                  f' , fun' ,
                  (x ⁺ , x⁺∈ω ,
                   antisym-⊆
                     (λ {k} k∈domf' →
                          subst (k ∈_)(dom∪ f (z ⁺) (next f z)) k∈domf'
                          ∶ k ∈ dom f ∪ ｛ z ⁺ ｝
                       |> map₂ (from ∈｛ z ⁺ ｝) ∘ from ∈∪ ∶ k ∈ dom f ∨ k ≡ z ⁺
                       |> map₁ (subst (k ∈_) dom≡z⁺) ∶ k ∈ z ⁺ ∨ k ≡ z ⁺
                       |> to ∈⁺)
                     (λ {k} k∈x⁺⁺ → case from ∈⁺ k∈x⁺⁺ of λ
                       { (inj₁ k∈z⁺) →
                            subst (k ∈_) (sym dom≡z⁺) k∈z⁺ ∶ k ∈ dom f
                         |> to ∈∪ ∘ inj₁ ∶ k ∈ dom f ∪ ｛ z ⁺ ｝
                         |> subst (k ∈_) (sym $ dom∪ f (z ⁺) (next f z))
                       ; (inj₂ refl) → to ∈dom $
                         next f x , to ∈∪ (inj₂ $ to ∈｛ _ ｝ refl)}) ,
                   (λ y ϕy →
                    begin f' [ ∅ ]
                            ≡⟨  f0 v₀ pv₀ ∶ f [ ∅ ] ≡ v₀
                             |> ∅∈⁺ z∈ω ,_ ∶ ∅ ∈ z ⁺ ∧ f [ ∅ ] ≡ v₀
                             |> Prod.map₁ (subst (∅ ∈_) $ sym dom≡z⁺)
                               ∶ ∅ ∈ dom f ∧ f [ ∅ ] ≡ v₀
                             |> from (fun [ ∅ ]≡ v₀) ∶ ⟨ ∅ ، v₀ ⟩ ∈ f
                             |> to ∈∪ ∘ inj₁
                               ∶ ⟨ ∅ ، v₀ ⟩ ∈ f ∪ ｛ ⟨ z ⁺ ، next f z ⟩ ｝
                             |> proj₂ ∘ to (fun' [ ∅ ]≡ v₀)⟩
                          v₀ ≡⟨ !v₀ ϕy ⟩
                          y ∎) ,
                   λ { {k} k∈dom' m n k≢z⁺ refl ψkmn →
                   case !next f' k ψkmn of λ { refl →
                   let k∈domf = subst (k ∈_) (dom∪ f (z ⁺) (next f z)) k∈dom'
                                ∶ k ∈ dom f ∪ ｛ z ⁺ ｝
                             |> map₂ (from ∈｛ _ ｝) ∘ from ∈∪
                                ∶ k ∈ dom f ∨ k ≡ z ⁺
                             |> fromInj₁ (⊥-elim ∘ k≢z⁺) ∶ k ∈ dom f
                       f'x≡fx : ∀{x} → x ∈ dom f → f' [ x ] ≡ f [ x ]
                       f'x≡fx {x} x∈dom =
                            fun [ x∈dom ∈dom] ∶ ⟨ x ، f [ x ] ⟩ ∈ f
                         |> to ∈∪ ∘ inj₁ ∶ ⟨ x ، f [ x ] ⟩ ∈ f'
                         |> proj₂ ∘ to (fun' [ x ]≡ (f [ x ]))
                   in case is? (k ≡ z) of λ
                   { (yes refl) →
                       f'x≡fx x∈dom ∶ f' [ z ] ≡ f [ z ]
                     |> cong (λ v → ⟨ z ⁺ ، elem $ !ψ x v ⟩) 
                       ∶ ⟨ z ⁺ ، next f' z ⟩ ≡ ⟨ z ⁺ ، next f z ⟩
                     |> to ∈∪ ∘ inj₂ ∘ to ∈｛ ⟨ z ⁺ ، next f z ⟩ ｝
                   ; (no k≢z) →
                        ψkmn ∶ ψ k (f' [ k ])(next f' k)
                     |> subst (λ v → ψ k v (next f' k)) (f'x≡fx k∈domf)
                        ∶ ψ k (f [ k ])(next f' k)
                     |> f⁺ k∈domf (f [ k ])(next f' k) k≢z refl
                        ∶ ⟨ k ⁺ ، next f' k ⟩ ∈ f
                     |> to ∈∪ ∘ inj₁}}}) ,
                  x⁺∈domf' , sym f'[x⁺]≡next
            in
            next f x , θx⁺next , λ {_} → let-rec-agree x⁺∈ω θx⁺next
          }}})
        ]
        where f₀ = ｛ ⟨ ∅ ، v₀ ⟩ ｝
              fun₀ = fun-｛⟨ ∅ ، v₀ ⟩｝
              dom∅≡ : dom f₀ ≡ ∅ ⁺
              dom∅≡ = begin dom ｛ ⟨ ∅ ، v₀ ⟩ ｝ ≡⟨ dom｛⟨ ∅ , v₀ ⟩｝ ⟩
                            ｛ ∅ ｝ ≡⟨ sym ∅-∪ ⟩
                            ∅ ⁺
                      ∎
              f₀[∅] : f₀ [ ∅ ] ≡ v₀
              f₀[∅] = proj₂ $ to (fun₀ [ ∅ ]≡ v₀) $ to ∈｛ ⟨ ∅ ، v₀ ⟩ ｝ refl
              θ∅v₀ =
                f₀ , fun₀ ,
                (∅ , ∅∈ω , dom∅≡ ,
                  (λ y ϕy → begin f₀ [ ∅ ] ≡⟨ f₀[∅] ⟩
                                  v₀ ≡⟨ !v₀ ϕy ⟩
                                  y ∎ ) ,
                  λ {x} x∈dom y z x≢∅ f₀[x]≡y ψxyz →
                    ⊥-elim $ x≢∅ $ from ∈｛ ∅ ｝ $
                    subst (x ∈_) (trans dom∅≡ ∅-∪) x∈dom) ,
                subst (∅ ∈_) (sym dom｛⟨ ∅ , v₀ ⟩｝) (to ∈｛ ∅ ｝ refl) ,
                sym f₀[∅]
