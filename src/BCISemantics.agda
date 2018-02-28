module BCISemantics where

  open import Syntax
  open import BCI

  open import Category.Monad

  open import Data.Empty
  open import Data.Fin using (Fin; zero; suc; fromℕ≤)
  open import Data.Maybe as M
  open import Data.Nat
  open import Data.Product

  open import Function
  open import Function.Equality
  open import Function.Inverse using (Inverse)

  open import Relation.Binary
  open import Relation.Binary.On as On
  open import Relation.Binary.Product.Pointwise
  open import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Binary.Sigma.Extras
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Product renaming (_×-dec_ to _×?_)

  Heap-size : Heap → ℕ → Set
  Heap-size h n = Inverse (Subset (≡.setoid ℕ) λ i → i ∈dom h)
                          (≡.setoid (Fin n))

  record Finite-heap : Set where
    constructor finite-heap
    field
      heap : Heap
      size : ℕ
      prf : Heap-size heap size

  _#F_ : Rel Finite-heap _
  _#F_ = _#_ on Finite-heap.heap

  zero-heap-¬∈dom : ∀ {i h} → Heap-size h zero → ¬ i ∈dom h
  zero-heap-¬∈dom {i} prf i∈ with to ⟨$⟩ (i , i∈)
    where
    open Inverse prf
  ... | ()

  #-dec : ∀ h0 h1 n0 n1 → Heap-size h0 n0 → Heap-size h1 n1 → Dec (h0 # h1)
  #-dec h0 h1 zero n1 prf0 prf1 = {!!}
  #-dec h0 h1 (suc n0) n1 prf0 prf1 =
    map′ {!!} {!!}
         ((i0 ∉dom? h1) ×? (#-dec h0′ h1 n0 n1 {!!} prf1))
    where
    open Inverse prf0

    i0 : ℕ
    i0 = proj₁ (from ⟨$⟩ zero)

    h0′ : Heap
    h0′ i with i ≟ i0
    ... | yes p = nothing
    ... | no ¬p = h0 i

  _#F?_ : Decidable _#F_
  finite-heap h0 zero prf0 #F? finite-heap h1 n1 prf1 =
    yes ((λ i∈h0 → ⊥-elim (zero-heap-¬∈dom prf0 i∈h0))
        , λ {i} _ → ¬∈dom→∉dom {i} {h0} (zero-heap-¬∈dom prf0))
  finite-heap h0 (suc n0) prf0 #F? finite-heap h1 n1 prf1 =
    map′ {!!} {!!}
         ((i0 ∉dom? h1) ×? (finite-heap {!h0′!} n0 {!!} #F? finite-heap h1 n1 prf1))
    where
    open Inverse prf0

    i0 : ℕ
    i0 = proj₁ (from ⟨$⟩ zero)

    h0′ : Heap
    h0′ i with i ≟ i0
    ... | yes p = nothing
    ... | no ¬p = h0 i

  apply : (x y : Heap × Val) → Maybe (Heap × Val)
  apply (h0 , v0) (h1 , v1) = {!_#_!}

  bci : BCI _ _
  bci = record
    { Carrier = Maybe (Heap × Val)
    ; _≈_ = Eq (_≗_ ×-Rel _≡_)
    ; _·_ = λ mhv0 mhv1 → mhv0 >>= λ hv0 →
                          mhv1 >>= λ hv1 →
                          apply hv0 hv1
    ; B = just {!!}
    ; C = just {!!}
    ; I = just {!!}
    ; isBCI = record
      { Bq = {!!}
      ; Cq = {!!}
      ; Iq = {!!}
      ; _·-cong_ = {!!}
      ; isEquivalence = Eq-isEquivalence (Setoid.isEquivalence (_ →-setoid _)
                                          ×-isEquivalence ≡.isEquivalence)
      }
    }
    where open RawMonad M.monad
