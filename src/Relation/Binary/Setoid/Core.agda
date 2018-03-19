module Relation.Binary.Setoid.Core where

  open import Data.Product

  open import Function.Equivalence

  open import Level

  open import Relation.Binary

  REL′ : ∀ {a al b bl A B} (_≈A_ : Rel {a} A al) (_≈B_ : Rel {b} B bl) l →
         Set (a ⊔ al ⊔ b ⊔ bl ⊔ suc l)
  REL′ {A = A} {B} _≈A_ _≈B_ l =
    ∃ λ (R : A → B → Set l) →
        ∀ {a a′ b b′} → a′ ≈A a → b ≈B b′ → R a b ⇔ R a′ b′

  Rel′ : ∀ {a al A} → Rel {a} A al → ∀ l → Set (a ⊔ al ⊔ suc l)
  Rel′ _≈_ l = REL′ _≈_ _≈_ l
