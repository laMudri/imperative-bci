module Relation.Binary.Sigma.Extras where

  open import Data.Unit

  open import Level

  open import Relation.Binary as B
  open import Relation.Binary.Indexed as I
  open import Relation.Binary.Sigma.Pointwise as Σ
  open import Relation.Binary.Simple as S
  open import Relation.Binary.Simple.Indexed as SI

  Subset : ∀ {a ℓ p} (A : B.Setoid a ℓ) (open B.Setoid A) → (Carrier → Set p) → B.Setoid _ _
  Subset {a} {ℓ} {p} A P = Σ.setoid A (SI.Always-setoid {ℓ = p} P)
