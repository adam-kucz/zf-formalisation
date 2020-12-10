{-# OPTIONS --exact-split #-}
module Foundation.Function.Reification where

open import Foundation.Axiom
open import Foundation.Relation.Base
open import Foundation.Pair
open import Foundation.Function.Base

module _ {X}(ϕ : (x y : set) → Set)(!ϕ : ⋀ x ∈ X , ∃! (ϕ x)) where

  private
    ϕ-pair : r-prop
    ϕ-pair x y = ∃ λ v → y ≡ ⟨ x ، v ⟩ ∧ ϕ x v
    !ϕ-pair : ⋀ x ∈ X , ∃! (ϕ-pair x)
    !ϕ-pair {x} x∈X = case !ϕ x∈X of λ
      { (y , ϕxy , !ϕxy) →
        ⟨ x ، y ⟩ ,
        (y , refl , ϕxy) ,
        λ { (y' , refl , ϕxy') → cong ⟨ x ،_⟩ $ !ϕxy ϕxy'}}

  open ≡-Reasoning 

  abstract
    reify : set
    reify = replacement ϕ-pair !ϕ-pair

    private ∈reify = ∈replacement ϕ-pair !ϕ-pair

    reify-is-fun : is-set-fun reify
    proj₁ reify-is-fun x∈f =
      case from (∈replacement ϕ-pair !ϕ-pair) x∈f of λ
      { (n , n∈ω , y , refl , _) → n , y , refl}
    proj₂ reify-is-fun {x}{y}{z} xy∈f xy'∈f =
      case from (∈replacement ϕ-pair !ϕ-pair) xy∈f ,
           from (∈replacement ϕ-pair !ϕ-pair) xy'∈f of λ
      { ((n , n∈ω , y' , xy≡ny' , ϕny') , m , m∈ω , z' , xz≡mz' , ϕmz') →
      case from ⟨,⟩≡ xy≡ny' , from ⟨,⟩≡ xz≡mz' of λ
      { ((refl , refl) , refl , refl) →
        let r , _ , !r = !ϕ n∈ω
        in begin y ≡⟨ sym $ !r ϕny' ⟩
                 r ≡⟨ !r ϕmz' ⟩
                 z ∎  }}
  
    reify-dom : dom reify ≡ X
    reify-dom = antisym-⊆
      (λ x∈dom → case from ∈dom x∈dom of λ
      { (v , xv∈f) → case from ∈reify xv∈f of λ
      { (x' , x'∈X , v' , xv≡x'v' , _) → case proj₁ $ from ⟨,⟩≡ xv≡x'v' of λ
      { refl → x'∈X }}})
      (λ {x} x∈X →
        let v , ϕv , _ = !ϕ x∈X
        in to ∈dom (v , to ∈reify (x , x∈X , v , refl , ϕv)))

    reify-valid : ⋀ x ∈ X , ϕ x (reify [ x ])
    reify-valid {x} x∈X = case from ∈reify ⟨x,r[x]⟩∈r of λ
      { (_ , _ , _ , xr[x]≡x'v , ϕx'v) → case from ⟨,⟩≡ xr[x]≡x'v of λ
      { (refl , refl) → ϕx'v}}
      where ⟨x,r[x]⟩∈r = reify-is-fun [ subst (x ∈_) (sym reify-dom) x∈X ∈dom]


module _ {f}(fun : is-set-fun f) where
  dereify : (x y : set) → Set
  dereify x y = ⟨ x ، y ⟩ ∈ f

  !dereify : ⋀ x ∈ dom f , ∃! (dereify x)
  !dereify x∈dom = let v , xv∈f = from ∈dom x∈dom
    in case proj₁ fun xv∈f of λ
    { (x' , y' , xv≡x'y') →
    case from ⟨,⟩≡ xv≡x'y' of λ
    { (refl , refl) → v , xv∈f , λ {_} → proj₂ fun xv∈f }}

