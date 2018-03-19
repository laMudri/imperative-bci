module BCI where

  open import Algebra.FunctionProperties

  open import Level

  open import Relation.Binary

  record IsBCI {a A ℓ} (_≈_ : Rel {a} A ℓ) (_·_ : Op₂ A) (B C I : A)
               : Set (a ⊔ ℓ) where
    infixl 8 _·-cong_
    field
      Bq : forall x y z -> (((B · x) · y) · z) ≈ (x · (y · z))
      Cq : forall x y z -> (((C · x) · y) · z) ≈ ((x · z) · y)
      Iq : forall x     ->             (I · x) ≈ x
      _·-cong_ : forall {x x' y y'} -> x ≈ x' -> y ≈ y' -> (x · y) ≈ (x' · y')
      isEquivalence : IsEquivalence _≈_

  record BCI c ℓ : Set (suc (c ⊔ ℓ)) where
    infixl 8 _·_
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ
      _·_   : Op₂ Carrier
      B C I : Carrier
      isBCI : IsBCI _≈_ _·_ B C I
    open IsBCI isBCI public

    setoid : Setoid c ℓ
    setoid = record { isEquivalence = isEquivalence }
    open Setoid setoid public
