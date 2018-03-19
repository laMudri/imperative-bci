module Relational.BCI where
  open import Algebra.FunctionProperties

  open import Data.Fin as F using (Fin)
  open import Data.Nat as N using (ℕ)
  open import Data.Vec as V

  open import Function

  open import Level

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  ----------------------------------------------------------
  -- Stuff for dealing with ternary operators acting like partial functions

  REL₃ : ∀ {a b c} (A : Set a) (B : Set b) (C : Set c) ℓ → Set _
  REL₃ A B C ℓ = A → B → C → Set ℓ

  Rel₃ : ∀ {a} (A : Set a) ℓ → Set _
  Rel₃ A = REL₃ A A A

  infixl 7 _`·_
  data Expr (n : ℕ) : Set where
    `var : (i : Fin n) → Expr n
    _`·_ : (x y : Expr n) → Expr n

  `#_ : ∀ m {n} {m<n : True (N.suc m N.≤? n)} → Expr n
  `#_ m {n} {m<n} = `var (F.#_ m {n} {m<n})

  equation_⟨_≈_⟩ : ∀ n (x y : Expr n) {a ℓ} {A : Set a} (var : Fin n → A)
                  (_≈_ : Rel A ℓ) (_·_≈_ : Rel₃ A ℓ) → Set (a ⊔ ℓ)
  equation_⟨_≈_⟩ n x y {a} {ℓ} {A} var _≈_ _·_≈_ =
    ∀ {X Y} → rel x X → rel y Y → X ≈ Y
    where
    rel : REL (Expr n) A (a ⊔ ℓ)
    rel (`var i) X = Lift {ℓ} {a} (var i ≈ X)
    rel (x `· y) Z = ∀ {X Y} → rel x X → rel y Y → X · Y ≈ Z

  module EquationBuilder {a ℓ A} (_≈_ : Rel {a} A ℓ) (_·_≈_ : Rel₃ A ℓ) where
    build⟨_≈_⟩ : ∀ {n} (x y : Expr n) (vs : Vec A n) → Set (a ⊔ ℓ)
    build⟨ x ≈ y ⟩ vs = equation _ ⟨ x ≈ y ⟩ (flip lookup vs) _≈_ _·_≈_

  ----------------------------------------------------------
  -- BCI algebra

  record IsBCI {a A ℓ} (_≈_ : Rel {a} A ℓ) (_·_≈_ : Rel₃ A ℓ) (B C I : A)
               : Set (a ⊔ ℓ) where
    open EquationBuilder _≈_ _·_≈_
    field
      Bq : ∀ x y z →
           build⟨ `# 0 `· `# 1 `· `# 2 `· `# 3 ≈ `# 1 `· (`# 2 `· `# 3) ⟩
           (B ∷ x ∷ y ∷ z ∷ [])
      Cq : ∀ x y z →
           build⟨ `# 0 `· `# 1 `· `# 2 `· `# 3 ≈ `# 1 `· `# 3 `· `# 2 ⟩
           (C ∷ x ∷ y ∷ z ∷ [])
      Iq : ∀ x → build⟨ `# 0 `· `# 1 ≈ `# 1 ⟩ (I ∷ x ∷ [])

      cong : ∀ {x x′ y y′ xy xy′} → x′ ≈ x → y′ ≈ y → xy ≈ xy′ →
             x · y ≈ xy → x′ · y′ ≈ xy′
      isEquivalence : IsEquivalence _≈_

  record BCI c ℓ : Set (suc (c ⊔ ℓ)) where
    infix 5 _·_≈_
    infix 4 _≈_
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ
      _·_≈_ : Rel₃ Carrier ℓ
      B C I : Carrier
      isBCI : IsBCI _≈_ _·_≈_ B C I
    open IsBCI isBCI public

    setoid : Setoid c ℓ
    setoid = record { isEquivalence = isEquivalence }
    open Setoid setoid public using (refl; sym; trans)

  record IsTotalBCI {a A ℓ} (_≈_ : Rel {a} A ℓ) (_·_ : Op₂ A) (B C I : A)
                    : Set (a ⊔ ℓ) where
    field
      Bq : ∀ x y z → (((B · x) · y) · z) ≈ (x · (y · z))
      Cq : ∀ x y z → (((C · x) · y) · z) ≈ ((x · z) · y)
      Iq : ∀ x     →             (I · x) ≈ x
      cong : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x · y) ≈ (x′ · y′)
      isEquivalence : IsEquivalence _≈_

  record TotalBCI c ℓ : Set (suc (c ⊔ ℓ)) where
    infix 5 _·_
    infix 4 _≈_
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ
      _·_ : Op₂ Carrier
      B C I : Carrier
      isTotalBCI : IsTotalBCI _≈_ _·_ B C I
    open IsTotalBCI isTotalBCI public

    setoid : Setoid c ℓ
    setoid = record { isEquivalence = isEquivalence }
    open Setoid setoid public using (refl; sym; trans)

    bci : BCI c ℓ
    bci = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _·_≈_ = λ x y xy → (x · y) ≈ xy
      ; B = B
      ; C = C
      ; I = I
      ; isBCI = record
        { Bq = λ x y z q q′ →
               trans (sym (q ((λ { Bxq (lift yq) → sym (cong (Bxq (lift refl) (lift refl)) yq) })) (lift refl)))
                     (trans (Bq x y z)
                            (q′ (lift refl) (λ { (lift yq) (lift zq) → sym (cong yq zq) })))
        ; Cq = λ x y z q q′ →
               trans (sym (q ((λ { Cxq (lift yq) → sym (cong (Cxq (lift refl) (lift refl)) yq) })) (lift refl)))
                     (trans (Cq x y z)
                            (q′ (λ { (lift xq) (lift zq) → sym (cong xq zq) }) (lift refl)))
        ; Iq = λ x q xq → trans (sym (q (lift refl) xq)) (Iq _)
        ; cong = λ xq yq xyq q → trans (cong xq yq) (trans q xyq)
        ; isEquivalence = isEquivalence
        }
      }

  ----------------------------------------------------------
  -- BCI polynomial syntax

  --infixl 7 _`·_ (defined above)
  infix 4 _↝_ _↭_ _↭*_

  data BCIs (n : ℕ) : Set where
    `var : Fin n → BCIs n
    `B `C `I : BCIs n
    _`·_ : (x y : BCIs n) → BCIs n

  data _↝_ {n} : (x y : BCIs n) → Set where
    Br : ∀ {x y z} → `B `· x `· y `· z ↝ x `· (y `· z)
    Cr : ∀ {x y z} → `C `· x `· y `· z ↝ x `· z `· y
    Ir : ∀ {x}     → `I `· x           ↝ x
    ·r-l : ∀ {x x′ y} → x ↝ x′ → x `· y ↝ x′ `· y
    ·r-r : ∀ {x y y′} → y ↝ y′ → x `· y ↝ x `· y′

  open import Data.RstClosure as RST
  open import Data.Star
  open import Data.Sum
  open import Data.SymClosure

  _↭_ : ∀ {n} (x y : BCIs n) → Set
  _↭_ = SymClosure _↝_

  _↭*_ : ∀ {n} (x y : BCIs n) → Set
  _↭*_ = RstClosure _↝_

  ·lr-l : ∀ {n} {x x′ y : BCIs n} → x ↭ x′ → x `· y ↭ x′ `· y
  ·lr-l (inj₁ x) = inj₁ (·r-l x)
  ·lr-l (inj₂ y) = inj₂ (·r-l y)

  ·lr-r : ∀ {n} {x y y′ : BCIs n} → y ↭ y′ → x `· y ↭ x `· y′
  ·lr-r (inj₁ x) = inj₁ (·r-r x)
  ·lr-r (inj₂ y) = inj₂ (·r-r y)

  _·lr*_ : ∀ {n} {x x′ y y′ : BCIs n} → x ↭* x′ → y ↭* y′ → x `· y ↭* x′ `· y′
  ε ·lr* ε = ε
  ε ·lr* (yr ◅ yrs) = ·lr-r yr ◅ ε ·lr* yrs
  (xr ◅ xrs) ·lr* yrs = ·lr-l xr ◅ xrs ·lr* yrs

  bcis-totalBCI : ℕ → TotalBCI zero zero
  bcis-totalBCI n = record
    { Carrier = BCIs n
    ; _≈_ = _↭*_
    ; _·_ = _`·_
    ; B = `B
    ; C = `C
    ; I = `I
    ; isTotalBCI = record
      { Bq = λ x y z → inj₁ Br ◅ ε
      ; Cq = λ x y z → inj₁ Cr ◅ ε
      ; Iq = λ x → inj₁ Ir ◅ ε
      ; cong = _·lr*_
      ; isEquivalence = Setoid.isEquivalence (RST.setoid _↝_)
      }
    }
