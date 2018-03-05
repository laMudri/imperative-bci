module BCISemantics where

  open import Syntax
  open import BCI

  open import Category.Monad

  open import Data.Empty
  open import Data.Fin using (Fin; zero; suc; fromℕ≤; punchOut; punchIn)
  open import Data.Maybe as M
  open import Data.Nat
  open import Data.Product
  open import Data.Unit using (⊤; tt)

  open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)

  open import Function
  open import Function.Equality
  open import Function.Inverse using (Inverse)

  open import Relation.Binary
  open import Relation.Binary.On as On
  open import Relation.Binary.Product.Pointwise
  open import Relation.Binary.PropositionalEquality as ≡
    hiding (cong)
  open import Relation.Binary.Sigma.Pointwise as ×P using (_,_; proj₁; proj₂)
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
      sz : Heap-size heap size

  _#F_ : Rel Finite-heap _
  _#F_ = _#_ on Finite-heap.heap

  zero-heap-¬∈dom : ∀ {i h} → Heap-size h zero → ¬ i ∈dom h
  zero-heap-¬∈dom {i} sz i∈ with to ⟨$⟩ (i , i∈)
    where
    open Inverse sz
  ... | ()

  delete : ℕ → Heap → Heap
  delete i h j with i ≟ j
  ... | yes p = nothing
  ... | no ¬p = h j

  delete-size : ∀ {i h n} →
                i ∈dom h → Heap-size h (suc n) → Heap-size (delete i h) n
  delete-size {i} {h} {n} i∈ sz = record
    { to = record { _⟨$⟩_ = {!to′!} ; cong = {!!} }
    ; from = {!from!}
    ; inverse-of = {!!}
    }
    where
    open Inverse sz
    open ≡-Reasoning

    to′ : ∃ (_∈dom delete i h) → Fin n
    to′ (j , j∈) with i ≟ j
    to′ (j , _ , ()) | yes i=j
    to′ (j , j∈) | no i≠j =
      punchOut {i = to ⟨$⟩ (i , i∈)} {to ⟨$⟩ (j , j∈)} λ eq →
        i≠j (begin
          i
            ≡⟨ ≡.sym (proj₁ (left-inverse-of (i , i∈))) ⟩
          proj₁ (from ⟨$⟩ (to ⟨$⟩ (i , i∈)))
            ≡⟨ proj₁ (cong from eq) ⟩
          proj₁ (from ⟨$⟩ (to ⟨$⟩ (j , j∈)))
            ≡⟨ proj₁ (left-inverse-of (j , j∈)) ⟩
          j
            ∎)

  #-dec : ∀ h0 h1 n0 n1 → Heap-size h0 n0 → Heap-size h1 n1 → Dec (h0 # h1)
  #-dec h0 h1 zero n1 sz0 sz1 = {!!}
  #-dec h0 h1 (suc n0) n1 sz0 sz1 =
    map′ {!!} {!!}
         ((i0 ∉dom? h1) ×? (#-dec (delete i0 h0) h1 n0 n1 {!!} sz1))
    where
    open Inverse sz0

    i0 : ℕ
    i0 = proj₁ (from ⟨$⟩ zero)

    --h0′ : Heap
    --h0′ i with i ≟ i0
    --... | yes p = nothing
    --... | no ¬p = h0 i

  _#F?_ : Decidable _#F_
  finite-heap h0 zero sz0 #F? finite-heap h1 n1 sz1 =
    yes ((λ i∈h0 → ⊥-elim (zero-heap-¬∈dom sz0 i∈h0))
        , λ {i} _ → ¬∈dom→∉dom {i} {h0} (zero-heap-¬∈dom sz0))
  finite-heap h0 (suc n0) sz0 #F? finite-heap h1 n1 sz1 =
    map′ {!!} {!!}
         ((i0 ∉dom? h1) ×? (finite-heap {!h0′!} n0 {!!} #F? finite-heap h1 n1 sz1))
    where
    open Inverse sz0

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
