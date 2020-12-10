{-# OPTIONS --exact-split #-}
module ZF.Relation where

open import ZF.Foundation hiding (id; _∘_)

id : set → set
id X = reify X X _≡_

infixr 25 _∘_
_∘_ : (P Q : set) → set
Q ∘ P = reify (dom P)(ran Q) λ x y → ∃ λ z → ⟨ x ، z ⟩ ∈ P ∧ ⟨ z ، y ⟩ ∈ Q

private variable X Y Z P Q R x y z : set

abstract
  id∈Rel : id X ∈ Rel X X
  id∈Rel = to ∈𝒫 λ x∈id → case from ∈reify x∈id of λ
    { (x , x , refl , x∈X , _ , refl) → to ⟨,⟩∈× (x∈X , x∈X)}

  ∘∈Rel : Q ∈ Rel Y Z → P ∈ Rel X Y →  Q ∘ P ∈ Rel X Z
  ∘∈Rel Q∈Rel P∈Rel = to ∈𝒫 λ x∈P∘Q → case from ∈reify x∈P∘Q of λ
    { (x , y , refl , x∈domP , y∈ranQ , _) →
      to ⟨,⟩∈× $ dom⊆ P∈Rel x∈domP , ran⊆ Q∈Rel y∈ranQ}

  id-∘ : P ∈ Rel X Y → id Y ∘ P ≡ P
  id-∘ P∈Rel = antisym-⊆
    (λ x∈id∘P → case from ∈reify x∈id∘P of λ
      { (u , v , refl , u∈X , v∈Y , z , uz∈P , zv∈id) →
      case from ⟨,⟩∈reify zv∈id of λ { (_ , _ , refl) → uz∈P}})
    (λ x∈P → case from ∈× $ from ∈𝒫 P∈Rel x∈P of λ
      { (u , u∈X , v , v∈Y , refl) →
        let vv∈id = to ⟨,⟩∈reify (v∈Y , v∈Y , refl) in
        to ⟨,⟩∈reify $
        to ∈dom (v , x∈P) , to ∈ran (v , vv∈id) , v , x∈P , vv∈id})

  ∘-id : P ∈ Rel X Y → P ∘ id X ≡ P
  ∘-id P∈Rel = antisym-⊆
    (λ x∈P∘id → case from ∈reify x∈P∘id of λ
      { (u , v , refl , u∈X , v∈Y , z , uz∈id , zv∈P) →
      case from ⟨,⟩∈reify uz∈id of λ { (_ , _ , refl) → zv∈P}})
    (λ x∈P → case from ∈× $ from ∈𝒫 P∈Rel x∈P of λ
      { (u , u∈X , v , v∈Y , refl) →
        let uu∈id = to ⟨,⟩∈reify (u∈X , u∈X , refl) in
        to ⟨,⟩∈reify $
        to ∈dom (u , uu∈id) , to ∈ran (u , x∈P) , u , uu∈id , x∈P})

  dom-id : dom (id X) ≡ X
  dom-id = antisym-⊆
    (λ x∈dom → case from ∈dom x∈dom of λ
      {(_ , xy∈id) → proj₁ $ from ⟨,⟩∈reify xy∈id})
    λ {x} x∈X → to ∈dom (x , to ⟨,⟩∈reify (x∈X , x∈X , refl))
  
  ran-id : ran (id X) ≡ X
  ran-id = antisym-⊆
    (λ x∈ran → case from ∈ran x∈ran of λ
      {(_ , xy∈id) → proj₁ $ proj₂ $ from ⟨,⟩∈reify xy∈id})
    λ {x} x∈X → to ∈ran (x , to ⟨,⟩∈reify (x∈X , x∈X , refl))

  -- dom-∘ : dom (P ∘ Q) ⊆ dom Q
  -- dom-∘ = {!!}
  
  -- ran-∘ : ran (P ∘ Q) ⊆ ran P
  -- ran-∘ = {!!}

  ∘-assoc : (P ∘ Q) ∘ R ≡ P ∘ (Q ∘ R)
  ∘-assoc {P} {Q} {R} = antisym-⊆
    (λ x∈[PQ]R → case from ∈reify x∈[PQ]R of λ
      { (x , z , refl , x∈domR , z∈ranPQ , y , xy∈R , yz∈PQ) →
      case from ⟨,⟩∈reify yz∈PQ of λ
      { (y∈domQ , z∈ranP , w , yw∈Q , wz∈P) → to ⟨,⟩∈reify $
      let xw∈QR = to ⟨,⟩∈reify $
            x∈domR , to ∈ran (y , yw∈Q) , y , xy∈R , yw∈Q
      in to ∈dom (w , xw∈QR) , z∈ranP , w , xw∈QR , wz∈P}})
    (λ x∈P[QR] → case from ∈reify x∈P[QR] of λ
      { (x , z , refl , x∈domQR , z∈ranP , y , xy∈QR , yz∈P) →
      case from ⟨,⟩∈reify xy∈QR of λ
      { (x∈domR , y∈ranQ , w , xw∈R , wy∈Q) → to ⟨,⟩∈reify $
      let wz∈PQ = to ⟨,⟩∈reify $
            to ∈dom (y , wy∈Q) , z∈ranP , y , wy∈Q , yz∈P
      in x∈domR , to ∈ran (w , wz∈PQ) , w , xw∈R , wz∈PQ }})
