module ImperativeBCI where

  open import Algebra
  open import Algebra.FunctionProperties
  open import Algebra.Structures

  open import Data.Empty
  open import Data.Fin using (Fin; fromℕ≤)
  open import Data.Maybe
  open import Data.Nat
  open import Data.Product
  open import Data.Sum
  open import Data.Unit using (⊤; tt)

  open import Level renaming (_⊔_ to _l⊔_; suc to lsuc)

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  --Cotransitive : ∀ {a ℓ A} → Rel {a} A ℓ → Set _
  --Cotransitive _#_ = ∀ {x y z} → x # y → (x # z) ⊎ (y # z)

  --record IsApartness {a ℓ ℓ′} {A : Set a} (≈ : Rel A ℓ) (# : Rel A ℓ′)
  --                   : Set (a l⊔ ℓ l⊔ ℓ′) where
  --  field
  --    isEquivalence : IsEquivalence ≈
  --    irreflexive : Irreflexive ≈ #
  --    sym : Symmetric #
  --    cotrans : Cotransitive #

  record IsPartialMonoid {a ℓ r A} (_≈_ : Rel {a} A ℓ) (_R_ : Rel A r)
                         (_•_⟨_⟩ : ∀ x y → x R y → A) (ε : A)
                         : Set (a l⊔ ℓ l⊔ r) where
    field
      identityTotal : (∀ y → ε R y) × (∀ x → x R ε)
      identity : (∀ y → (ε • y ⟨ proj₁ identityTotal y ⟩) ≈ y)
               × (∀ x → (x • ε ⟨ proj₂ identityTotal x ⟩) ≈ x)
      distrib : (∀ {x y z} → x R z → y R z → (xy : x R y) → (x • y ⟨ xy ⟩) R z)
              × (∀ {x y z} → x R y → x R z → (yz : y R z) → x R (y • z ⟨ yz ⟩))

  record PartialMonoid c ℓ r : Set (lsuc (c l⊔ ℓ l⊔ r)) where
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ
      _R_ : Rel Carrier r
      _•_⟨_⟩ : ∀ x y → x R y → Carrier
      ε : Carrier
      isPartialMonoid : IsPartialMonoid _≈_ _R_ _•_⟨_⟩ ε

  --record IsHeap {a ℓ ℓ′} {A : Set a}
  --              (≈ : Rel A ℓ) (# : Rel A ℓ′) (• : Op₂ A) (ε : A)
  --              : Set (a l⊔ ℓ l⊔ ℓ′) where
  --  field
  --    isMonoid : IsMonoid ≈ • ε
  --    isApartness : IsApartness ≈ #

  --record Heap c ℓ ℓ′ : Set (lsuc (c l⊔ ℓ l⊔ ℓ′)) where
  --  field
  --    Carrier : Set c
  --    _≈_ : Rel Carrier ℓ
  --    _#_ : Rel Carrier ℓ′
  --    _•_ : Op₂ Carrier
  --    ε : Carrier

  postulate
    Op : Set
    ⟦_⟧op : Op → Op₂ ℕ

  -- l: the number of variables bound by let/λ
  data Val : Set
  data Exp (l : ℕ) : Set

  Env : (l : ℕ) → Set
  Env l = Fin l → Val

  data Val where
    nat : ℕ → Val
    clo : ∀ {l} → Exp (suc l) → Env l → Val

  data Exp l where
    var : (x : Fin l) → Exp l
    if0_then_else_ : (x : Fin l) (et ef : Exp l) → Exp l
    let-rd_,,_ : (x : Fin l) (e : Exp (suc l)) → Exp l
    wr[_,_],,_ : (x y : Fin l) (e : Exp l) → Exp l
    let-op_[_,_],,_ : (f : Op) (x y : Fin l) (e : Exp (suc l)) → Exp l
    let-app[_,_],,_ : (x y : Fin l) (e : Exp (suc l)) → Exp l
    let-lam_,,_ : (e′ : Exp (suc l)) (e : Exp (suc l)) → Exp l
    let-val_,,_ : (v : Val) (e : Exp (suc l)) → Exp l

  Heap : Set
  Heap = ℕ → Maybe ℕ

  infixl 5 _-,_
  _-,_ : ∀ {a n} {A : Set a} → (Fin n → A) → A → (Fin (suc n) → A)
  (f -, x) Fin.zero = x
  (f -, x) (Fin.suc i) = f i

  _∈dom_ : ℕ → Heap → Set
  i ∈dom h with h i
  i ∈dom h | just x = ⊤
  i ∈dom h | nothing = ⊥

  _∈dom′_ : ℕ → Heap → Set
  i ∈dom′ h = ∃ λ n → h i ≡ just n

  write : ℕ → ℕ → Heap → Heap
  write i n h j with i ≟ j
  write i n h j | yes p = just n
  write i n h j | no ¬p = h j

  read : ∀ {i h} → i ∈dom h → ℕ
  read {i} {h} d with h i
  read {i} {h} d | just n = n
  read {i} {h} () | nothing

  read′ : ∀ {i h} → i ∈dom′ h → ℕ
  read′ (n , eq) = n

  infix 3 _,_,_⇓_,_
  data _,_,_⇓_,_ {l} (h : Heap) (η : Env l) : Exp l → Heap → Val → Set where
    e-if0-t : ∀ {x et ef h′ vt} →
              η x ≡ nat 0 → h , η , et ⇓ h′ , vt
              →
              h , η , if0 x then et else ef ⇓ h′ , vt
    e-if0-f : ∀ {x et ef h′ vf} →
              η x ≢ nat 0 → h , η , ef ⇓ h′ , vf
              →
              h , η , if0 x then et else ef ⇓ h′ , vf
    e-rd : ∀ {x e h′ i v} →
           η x ≡ nat i → (d : i ∈dom′ h) → h , η -, nat (read′ {i} {h} d) , e ⇓ h′ , v
           →
           h , η , let-rd x ,, e ⇓ h′ , v
    e-wr : ∀ {x y e h′ v i n} →
           η x ≡ nat i → η y ≡ nat n → n ∈dom′ h → write i n h , η , e ⇓ h′ , v
           →
           h , η , wr[ x , y ],, e ⇓ h′ , v
    e-op : ∀ {f x y e h′ v m n} →
           η x ≡ nat m → η y ≡ nat n →
           h , η -, nat (⟦ f ⟧op m n) , e ⇓ h′ , v
           →
           h , η , let-op f [ x , y ],, e ⇓ h′ , v
    e-app : ∀ {x y e h′ v ll vl el ηl hl} →
            η x ≡ clo {ll} el ηl →
            h , ηl -, η y , el ⇓ hl , vl → hl , η -, vl , e ⇓ h′ , v
            →
            h , η , let-app[ x , y ],, e ⇓ h′ , v
    e-lam : ∀ {el e h′ v} →
            h , η -, clo el η , e ⇓ h′ , v
            →
            h , η , let-lam el ,, e ⇓ h′ , v
    e-val : ∀ {v′ e h′ v} →
            h , η -, v′ , e ⇓ h′ , v
            →
            h , η , let-val v′ ,, e ⇓ h′ , v
    e-var : ∀ {x} → h , η , var x ⇓ h , η x

  deterministic : ∀ {l h η} {e : Exp l} {h0 v0 h1 v1} →
                  h , η , e ⇓ h0 , v0 → h , η , e ⇓ h1 , v1 →
                  h0 ≡ h1 × v0 ≡ v1
  deterministic (e-if0-t q0 r0) (e-if0-t q1 r1) = deterministic r0 r1
  deterministic (e-if0-t q0 r0) (e-if0-f nq1 r1) = ⊥-elim (nq1 q0)
  deterministic (e-if0-f nq0 r0) (e-if0-t q1 r1) = ⊥-elim (nq0 q1)
  deterministic (e-if0-f nq0 r0) (e-if0-f nq1 r1) = deterministic r0 r1
  deterministic (e-rd q0 (n0 , nq0) r0) (e-rd q1 (n1 , nq1) r1) rewrite q0 with tt
  deterministic (e-rd q0 (n0 , nq0) r0) (e-rd refl (n1 , nq1) r1) | tt rewrite nq0 with tt
  deterministic (e-rd q0 (n0 , nq0) r0) (e-rd refl (.n0 , refl) r1) | tt | tt = deterministic r0 r1
  -- FIXME: more/less readable style?
  --deterministic {l} {h} {η} (e-wr {x} {y} xq0 yq0 (n0 , nq0) r0)
  --                          (e-wr xq1 yq1 (n1 , nq1) r1)
  --  with η x | η y
  --deterministic {l} {h} {η} (e-wr {x} {y} {i = i} {n} refl refl (n0 , nq0) r0)
  --                          (e-wr refl refl (n1 , nq1) r1)
  --  | .(nat i) | .(nat n) with h n
  --deterministic {l} {h} {η} (e-wr {x} {y} {i = i} {n} refl refl (n0 , refl) r0)
  --                          (e-wr refl refl (.n0 , refl) r1)
  --  | .(nat i) | .(nat n) | .(just n0) = deterministic r0 r1
  deterministic (e-wr xq0 yq0 (n0 , nq0) r0) (e-wr xq1 yq1 (n1 , nq1) r1) rewrite xq0 | yq0 with tt
  deterministic (e-wr xq0 yq0 (n0 , nq0) r0) (e-wr refl refl (n1 , nq1) r1) | tt rewrite nq0 with tt
  deterministic (e-wr xq0 yq0 (n0 , nq0) r0) (e-wr refl refl (n1 , refl) r1) | tt | tt = deterministic r0 r1
  deterministic (e-op xq0 yq0 r0) (e-op xq1 yq1 r1) rewrite xq0 | yq0 with tt
  deterministic (e-op xq0 yq0 r0) (e-op refl refl r1) | tt = deterministic r0 r1
  deterministic (e-app q0 r0′ r0) (e-app q1 r1′ r1) rewrite q0 with tt
  deterministic (e-app q0 r0′ r0) (e-app refl r1′ r1) | tt with deterministic r0′ r1′
  deterministic (e-app q0 r0′ r0) (e-app refl r1′ r1) | tt | (refl , refl) = deterministic r0 r1
  deterministic (e-lam r0) (e-lam r1) = deterministic r0 r1
  deterministic (e-val r0) (e-val r1) = deterministic r0 r1
  deterministic e-var e-var = refl , refl
