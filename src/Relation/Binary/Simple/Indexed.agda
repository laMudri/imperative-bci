module Relation.Binary.Simple.Indexed where

  open import Relation.Binary.Simple using (Const)
  open import Relation.Binary.Indexed
  open import Data.Unit
  open import Data.Empty
  open import Level

  Always : ∀ {i a ℓ} {I : Set i} {A : I → Set a} {j k} → A j → A k → Set ℓ
  Always = Const (Lift ⊤)

  Always-setoid : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Setoid I a ℓ
  Always-setoid A = record
    { Carrier = A
    ; _≈_ = λ {i} {j} → Always {j = i} {j}
    ; isEquivalence = record { }
    }

  Never : ∀ {i a ℓ} {I : Set i} {A : I → Set a} {j k} → A j → A k → Set ℓ
  Never = Const (Lift ⊥)
