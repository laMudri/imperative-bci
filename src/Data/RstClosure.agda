module Data.RstClosure where

  open import Data.Star
  open import Data.Sum
  open import Data.SymClosure as Sym

  open import Function

  open import Level

  open import Relation.Binary

  RstClosure : ∀ {i t I} → Rel {i} I t → Rel I (i ⊔ t)
  RstClosure = Star ∘ SymClosure

  setoid : ∀ {i t I} → Rel {i} I t → Setoid _ _
  setoid {i} {t} {I} R = record
    { Carrier = I
    ; _≈_ = RstClosure R
    ; isEquivalence = record
      { refl = ε
      ; sym = sym′
      ; trans = _◅◅_
      }
    }
    where
    sym′ : Symmetric (RstClosure R)
    sym′ ε = ε
    sym′ (x ◅ xs) = sym′ xs ◅◅ Sym.sym R x ◅ ε
