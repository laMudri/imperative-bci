module Algebra.FunctionProperties.Partial.Core where

  open import Level

  open import Relation.Binary

  _⇀_ : ∀ {a al b bl} → Setoid a al → Setoid b bl → Setoid {!!} {!!}
  A ⇀ B = record
    { Carrier = {!!}
    ; _≈_ = {!!}
    ; isEquivalence = {!!}
    }
    where
    module A = Setoid A; module B = Setoid B

  --Op₁ : 
