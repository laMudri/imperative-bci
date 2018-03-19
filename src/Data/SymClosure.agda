module Data.SymClosure where

  open import Data.Sum

  open import Level

  open import Relation.Binary

  SymClosure : ∀ {i t I} → Rel {i} I t → Rel I t
  SymClosure R x y = R x y ⊎ R y x

  sym : ∀ {i t I} (R : Rel {i} I t) → Symmetric (SymClosure R)
  sym R (inj₁ xy) = inj₂ xy
  sym R (inj₂ yx) = inj₁ yx
