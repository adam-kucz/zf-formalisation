{-# OPTIONS --exact-split #-}
module ZF.Function where

open import ZF.Foundation hiding (id; _∘_; _[_]'; _[_]≡_; _[_∈dom])
open import ZF.Foundation.Function.Base as Base
  hiding (_[_]'; _[_]≡_; _[_∈dom]) public

_∶_⇀_ : (R X Y : set) → Set
R ∶ X ⇀ Y =
  (∀{x y y'} → ⟨ x ، y ⟩ ∈ R → ⟨ x ، y' ⟩ ∈ R → y ≡ y') ∧
  R ∈ Rel X Y

_∶_⟶_ : (R X Y : set) → Set
R ∶ X ⟶ Y = dom R ≡ X ∧ R ∶ X ⇀ Y

Fun _⇒_ : (X Y : set) → set
X ⇒ Y = ｛ f ∈ Rel X Y ∣ f ∶ X ⟶ Y ｝
Fun = _⇒_

open import ZF.Relation
open import Function.Reasoning
open ≡-Reasoning
  
private variable X Y Z f g h x y z : set
  
--- Properties of partial functions
  
abstract
  id-is-partial-fun : id X ∶ X ⇀ X
  id-is-partial-fun =
    (λ {x}{y}{y'} xy∈R xy'∈R →
    begin y ≡⟨ sym $ proj₂ $ proj₂ $ from ⟨,⟩∈reify xy∈R ⟩
          x ≡⟨ proj₂ $ proj₂ $ from ⟨,⟩∈reify xy'∈R ⟩
          y' ∎) ,
    id∈Rel
  
  ∘-is-partial-fun : g ∶ Y ⇀ Z → f ∶ X ⇀ Y → g ∘ f ∶ X ⇀ Z
  ∘-is-partial-fun (g-func , g∈Rel) (f-func , f∈Rel) =  
    (λ {x}{y}{y'} xy∈gf xy'∈gf →
    case from ⟨,⟩∈reify xy∈gf , from ⟨,⟩∈reify xy'∈gf of λ
    { ((_ , _ , z , xz∈f , zy∈g) , (_ , _ , z' , xz'∈f , z'y'∈g)) →
       f-func xz∈f xz'∈f ∶ z ≡ z'
    |> (λ {refl → g-func zy∈g z'y'∈g}) ∶ y ≡ y'}) ,
    ∘∈Rel g∈Rel f∈Rel
  
  --- Properties of functions
  
  ∶⟶→is-set-fun : f ∶ X ⟶ Y → is-set-fun f
  ∶⟶→is-set-fun (_ , f-fun , f∈Rel) =
    (λ x∈f → case from ∈× $ from ∈𝒫 f∈Rel x∈f of λ
      { (x , _ , y , _ , refl) → x , y , refl} ) ,
    f-fun
  
  _[_∈dom] : f ∶ X ⟶ Y → ⋀ x ∈ X , ⟨ x ، f [ x ] ⟩ ∈ f
  f@(refl , _) [ x∈X ∈dom] = ∶⟶→is-set-fun f Base.[ x∈X ∈dom]
  
  _[_]≡ : f ∶ X ⟶ Y → (x : set) → (x ∈ X ∧ f [ x ] ≡ y) ⇔ ⟨ x ، y ⟩ ∈ f
  f@(refl , _) [ x ]≡ = mk⇔
    (λ { (x∈X , refl) → f [ x∈X ∈dom]})
    (λ { xy∈f → to (∶⟶→is-set-fun f Base.[ x ]≡ _) xy∈f})
  
  val∈ran : f ∶ X ⟶ Y → ⋀ x ∈ X , f [ x ] ∈ Y
  val∈ran f@(_ , _ , f∈Rel) x∈X =
    proj₂ $ from ⟨,⟩∈× $ from ∈𝒫 f∈Rel $ f [ x∈X ∈dom]

  fun-ext : ∀{f'}{funf : f ∶ X ⟶ Y}{funf' : f' ∶ X ⟶ Y} →
    (⋀ x ∈ X , f [ x ] ≡ f' [ x ])
    → ----------------------------------------
    f ≡ f'
  fun-ext {f}{f' = f'}{funf@(refl , _ , f∈Rel)}
          {funf'@(dom'≡dom , _ , f'∈Rel)} ∀x,fx≡f'x = antisym-⊆
    (λ x∈f → case from ∈× $ from ∈𝒫 f∈Rel x∈f of λ
      { (u , u∈domf , v , v∈Y , refl) →
      case proj₂ $ to (funf [ u ]≡) x∈f of λ
      { refl → funf' [ u∈domf  ∈dom] ∶ ⟨ u ، f' [ u ] ⟩ ∈ f'
            |> subst (λ v → ⟨ u ، v ⟩ ∈ f') (sym $ ∀x,fx≡f'x u∈domf)}})
    (λ x∈f' → case from ∈× $ from ∈𝒫 f'∈Rel x∈f' of λ
      { (u , u∈domf' , v , v∈Y , refl) →
      case proj₂ $ to (funf' [ u ]≡) x∈f' of λ
      { refl → funf [ u∈domf' ∈dom] ∶ ⟨ u ، f [ u ] ⟩ ∈ f
            |> subst (λ v → ⟨ u ، v ⟩ ∈ f) (∀x,fx≡f'x u∈domf')}})

  id-is-fun : id X ∶ X ⟶ X
  id-is-fun =
    antisym-⊆
      (λ x∈dom → case from ∈dom x∈dom of λ
        { (_ , xx'∈id) → proj₁ $ from ⟨,⟩∈reify xx'∈id})
      (λ {x} x∈X → to ∈dom $ x , to ⟨,⟩∈reify (x∈X , x∈X , refl)) ,
    id-is-partial-fun
  
  open import ZF.Foundation.Axiom.Nonconstructive
  open import Relation.Nullary
  
  ∘-is-fun : g ∶ Y ⟶ Z → f ∶ X ⟶ Y → g ∘ f ∶ X ⟶ Z
  ∘-is-fun {g}{f = f} fung@(refl , g⇀) funf@(refl , f⇀) =
    antisym-⊆
      (λ x∈domgf → case from ∈dom x∈domgf of λ
        { (v , xv∈gf) → proj₁ $ from ⟨,⟩∈reify xv∈gf })
      (λ {x} x∈domf → case from ∈dom x∈domf of λ
        { (fx , xfx∈f) → case proj₂ $ to (funf [ x ]≡) xfx∈f of λ
        { refl → let fxgfx∈g = fung [ val∈ran funf x∈domf ∈dom] in
          to ∈dom $
          g [ fx ] ,
          to ⟨,⟩∈reify (x∈domf , to ∈ran (fx , fxgfx∈g) , fx , xfx∈f , fxgfx∈g)
        }}) ,
    ∘-is-partial-fun g⇀ f⇀
  
  ∘[]≡ : g ∶ Y ⟶ Z → f ∶ X ⟶ Y → ⋀ x ∈ X , g ∘ f [ x ] ≡ g [ f [ x ] ]
  ∘[]≡ {f = f} fung@(refl , g-fun , _) funf@(refl , f-fun , _) {x} x∈X =
    let fun∘ = ∘-is-fun fung funf
        fxgfx∈g = fung [ val∈ran funf x∈X ∈dom] in
    proj₂ $ to (fun∘ [ x ]≡) $ to ⟨,⟩∈reify $
    x∈X , to ∈ran (f [ x ] , fxgfx∈g) , f [ x ] , funf [ x∈X ∈dom] , fxgfx∈g
  
  dom-∘ : g ∶ Y ⟶ Z → f ∶ X ⟶ Y → dom (g ∘ f) ≡ X
  dom-∘ {g}{f = f} fung@(refl , _) funf@(refl , _) = antisym-⊆
    (λ x∈domgf → case from ∈dom x∈domgf of λ
      { (v , xv∈gf) → proj₁ $ from ⟨,⟩∈reify xv∈gf})
    (λ {x} x∈domf → to ∈dom $
      let fxgfx∈g = fung [ val∈ran funf x∈domf ∈dom]
      in
      g [ f [ x ] ] ,
      to ⟨,⟩∈reify (
        x∈domf ,
        to ∈ran (f [ x ] , fxgfx∈g) ,
        f [ x ] ,
        funf [ x∈domf ∈dom] ,
        fxgfx∈g))

retraction : (g f : set) → Set
retraction g f = g ∘ f ≡ id (dom f) 
  
section : (g f : set) → Set
section g f = f ∘ g ≡ id (dom g) 

bijection : f ∶ X ⟶ Y → Set
bijection {f}{X}{Y} _ = ∃ λ g → retraction g f ∧ section g f ∧ g ∶ Y ⟶ X
  
abstract
  biejction-id : bijection (id-is-fun {X})
  biejction-id {X} =
    id X ,
    (subst (λ Y → id X ∘ id X ≡ id Y) (sym dom-id) $ id-∘ id∈Rel) ,
    (subst (λ Y → id X ∘ id X ≡ id Y) (sym dom-id) $ id-∘ id∈Rel) ,
    id-is-fun
  
  biejction-∘ : {fung : g ∶ Y ⟶ Z}{funf : f ∶ X ⟶ Y} →
    bijection fung →
    bijection funf →
    bijection (∘-is-fun fung funf)
  biejction-∘ {g}{f = f}{fung = fung@(refl , _ , g∈Rel)}
              {funf@(refl , _ , f∈Rel)}
              (g⁻¹ , g⁻¹g≡id , gg⁻¹≡id , g⁻¹-fun@(refl , _ , g⁻¹∈Rel))
              (f⁻¹ , f⁻¹f≡id , ff⁻¹≡id , f⁻¹-fun@(domf⁻¹≡ , _)) =
    f⁻¹ ∘ g⁻¹ ,
    (begin (f⁻¹ ∘ g⁻¹) ∘ g ∘ f ≡⟨ ∘-assoc ⟩
           f⁻¹ ∘ g⁻¹ ∘ g ∘ f ≡⟨ cong (f⁻¹ ∘_) $ sym ∘-assoc ⟩
           f⁻¹ ∘ (g⁻¹ ∘ g) ∘ f ≡⟨ cong (λ x → f⁻¹ ∘ x ∘ f) g⁻¹g≡id ⟩
           f⁻¹ ∘ id _ ∘ f ≡⟨ cong (f⁻¹ ∘_) (id-∘ f∈Rel) ⟩
           f⁻¹ ∘ f ≡⟨ subst (λ A → f⁻¹ ∘ f ≡ id A)
                            (sym $ dom-∘ fung funf) f⁻¹f≡id ⟩
           id _ ∎) ,
    (begin (g ∘ f) ∘ f⁻¹ ∘ g⁻¹ ≡⟨ ∘-assoc ⟩
           g ∘ f ∘ f⁻¹ ∘ g⁻¹ ≡⟨ cong (g ∘_) $ sym ∘-assoc ⟩
           g ∘ (f ∘ f⁻¹) ∘ g⁻¹ ≡⟨ cong (λ x → g ∘ x ∘ g⁻¹) ff⁻¹≡id ⟩
           g ∘ id _ ∘ g⁻¹ ≡⟨ cong (g ∘_) $
                             subst (λ A → id A ∘ g⁻¹ ≡ g⁻¹)
                                   (sym domf⁻¹≡) $
                             id-∘ g⁻¹∈Rel ⟩
           g ∘ g⁻¹ ≡⟨ subst (λ A → g ∘ g⁻¹ ≡ id A)
                            (sym $ dom-∘ f⁻¹-fun g⁻¹-fun) gg⁻¹≡id ⟩
           id _ ∎) ,
    ∘-is-fun f⁻¹-fun g⁻¹-fun
