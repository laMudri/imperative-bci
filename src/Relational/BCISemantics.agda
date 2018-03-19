module Relational.BCISemantics where

  open import Relational.Syntax
  --open import Relational.BCI

  open import Category.Monad

  open import Data.Empty
  open import Data.Fin using (Fin; zero; suc; fromℕ≤; punchOut; punchIn)
  open import Data.Maybe as M
  open import Data.Nat
  open import Data.Product
  --open import Relation.Binary.Product.Pointwise
  open import Data.Product.Relation.Pointwise.Dependent as ×P
    using (_,_; proj₁; proj₂)
  open import Data.Unit using (⊤; tt)

  open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)

  open import Function
  open import Function.Equality hiding (id; _∘_)
  open import Function.Inverse using (Inverse)

  open import Relation.Binary
  open import Relation.Binary.On as On
  open import Relation.Binary.PropositionalEquality as ≡
    hiding (cong)
  open import Relation.Binary.Sigma.Extras
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Product renaming (_×-dec_ to _×?_)

  delete : ℕ → Heap → Heap
  delete i h j with i ≟ j
  ... | yes p = nothing
  ... | no ¬p = h j

  apply : (x y xy : Heap × Val) → Set
  apply (h0 , v0) (h1 , v1) (h2 , v2) = {!_#_!}

  --bci : BCI _ _
  --bci = record
  --  { Carrier = Maybe (Heap × Val)
  --  ; _≈_ = Eq (_≗_ ×-Rel _≡_)
  --  ; _·_ = λ mhv0 mhv1 → mhv0 >>= λ hv0 →
  --                        mhv1 >>= λ hv1 →
  --                        apply hv0 hv1
  --  ; B = just {!!}
  --  ; C = just {!!}
  --  ; I = just {!!}
  --  ; isBCI = record
  --    { Bq = {!!}
  --    ; Cq = {!!}
  --    ; Iq = {!!}
  --    ; _·-cong_ = {!!}
  --    ; isEquivalence = Eq-isEquivalence (Setoid.isEquivalence (_ →-setoid _)
  --                                        ×-isEquivalence ≡.isEquivalence)
  --    }
  --  }
  --  where open RawMonad M.monad
