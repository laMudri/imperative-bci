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

  open import Function

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
  i ∈dom h = ∃ λ n → h i ≡ just n

  _∉dom_ : ℕ → Heap → Set
  i ∉dom h = h i ≡ nothing

  ¬∈dom→∉dom : ∀ {i h} → ¬ (i ∈dom h) → i ∉dom h
  ¬∈dom→∉dom {i} {h} ref with h i
  ... | just x = ⊥-elim (ref (x , refl))
  ... | nothing = refl

  ∉dom→¬∈dom : ∀ {i h} → i ∉dom h → ¬ i ∈dom h
  ∉dom→¬∈dom {i} {h} i∉ (n , q) with h i
  ∉dom→¬∈dom {i} {h} refl (n , ()) | .nothing

  write : ℕ → ℕ → Heap → Heap
  write i n h j with i ≟ j
  ... | yes p = just n
  ... | no ¬p = h j

  write-ext : ∀ i n {h h′} → h ≗ h′ → write i n h ≗ write i n h′
  write-ext i n hq j with i ≟ j
  ... | yes p = refl
  ... | no ¬p = hq j

  read : ∀ {i h} → i ∈dom h → ℕ
  read (n , eq) = n

  infix 3 _,_,_⇓_,_
  data _,_,_⇓_,_ {l} (h : Heap) (η : Env l) : Exp l → Heap → Val → Set where
    e-if0-t : ∀ {x et ef h′ vt} →
              (q : η x ≡ nat 0) → h , η , et ⇓ h′ , vt
              →
              h , η , if0 x then et else ef ⇓ h′ , vt
    e-if0-f : ∀ {x et ef h′ vf} →
              (¬q : η x ≢ nat 0) → h , η , ef ⇓ h′ , vf
              →
              h , η , if0 x then et else ef ⇓ h′ , vf
    e-rd : ∀ {x e h′ i v} →
           (q : η x ≡ nat i) (i∈ : i ∈dom h) →
           h , η -, nat (read {i} {h} i∈) , e ⇓ h′ , v
           →
           h , η , let-rd x ,, e ⇓ h′ , v
    e-wr : ∀ {x y e h′ v i n} →
           (xq : η x ≡ nat i) (yq : η y ≡ nat n) (i∈ : i ∈dom h) →
           write i n h , η , e ⇓ h′ , v
           →
           h , η , wr[ x , y ],, e ⇓ h′ , v
    e-op : ∀ {f x y e h′ v m n} →
           (xq : η x ≡ nat m) (yq : η y ≡ nat n) →
           h , η -, nat (⟦ f ⟧op m n) , e ⇓ h′ , v
           →
           h , η , let-op f [ x , y ],, e ⇓ h′ , v
    e-app : ∀ {x y e h′ v ll vl el ηl hl} →
            (q : η x ≡ clo {ll} el ηl) →
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
    e-var : ∀ {x h′}
            (q : h ≗ h′)
            →
            h , η , var x ⇓ h′ , η x

  --⇓-ext : ∀ {l h h′ η η′} {e e′ : Exp l} {hv hv′ v v′} →
  --        h ≗ h′ → η ≗ η′ → e ≡ e′ → hv ≗ hv′ → v ≡ v′ →
  --        h , η , e ⇓ hv , v → h′ , η′ , e′ ⇓ hv′ , v′

  ⇓-ext-h : ∀ {l h h′ η} {e : Exp l} {hv v} → h ≗ h′ →
            h , η , e ⇓ hv , v → h′ , η , e ⇓ hv , v
  ⇓-ext-h hq (e-if0-t q r) = e-if0-t q (⇓-ext-h hq r)
  ⇓-ext-h hq (e-if0-f ¬q r) = e-if0-f ¬q (⇓-ext-h hq r)
  ⇓-ext-h {l} {h} {h′} hq (e-rd {i = i} q (n , nq) r) =
    e-rd q (n , trans (sym (hq i)) nq) (⇓-ext-h hq r)
  ⇓-ext-h hq (e-wr {i = i} xq yq (n , nq) r) =
    e-wr xq yq (n , trans (sym (hq i)) nq) (⇓-ext-h (write-ext i _ hq) r)
  ⇓-ext-h hq (e-op xq yq r) = e-op xq yq (⇓-ext-h hq r)
  ⇓-ext-h hq (e-app q r′ r) = e-app q (⇓-ext-h hq r′) r
  ⇓-ext-h hq (e-lam r) = e-lam (⇓-ext-h hq r)
  ⇓-ext-h hq (e-val r) = e-val (⇓-ext-h hq r)
  ⇓-ext-h hq (e-var q) = e-var (λ i → trans (sym (hq i)) (q i))

  deterministic : ∀ {l h0 h1 η} {e : Exp l} {hv0 v0 hv1 v1} → h0 ≗ h1 →
                  h1 , η , e ⇓ hv0 , v0 → h0 , η , e ⇓ hv1 , v1 →
                  hv0 ≗ hv1 × v0 ≡ v1
  deterministic hq (e-if0-t q0 r0) (e-if0-t q1 r1) = deterministic hq r0 r1
  deterministic hq (e-if0-t q0 r0) (e-if0-f nq1 r1) = ⊥-elim (nq1 q0)
  deterministic hq (e-if0-f nq0 r0) (e-if0-t q1 r1) = ⊥-elim (nq0 q1)
  deterministic hq (e-if0-f nq0 r0) (e-if0-f nq1 r1) = deterministic hq r0 r1
  deterministic {l} {h0} {h1} {η} {let-rd x ,, e} hq
                (e-rd iq0 (n0 , nq0) r0) (e-rd iq1 (n1 , nq1) r1)
                with η x
  deterministic {l} {h0} {h1} {η} {let-rd x ,, e} hq
                (e-rd refl (n0 , nq0) r0) (e-rd refl (n1 , nq1) r1)
                | nat i rewrite hq i with h1 i
  deterministic {l} {h0} {h1} {η} {let-rd x ,, e} hq
                (e-rd refl (n0 , refl) r0) (e-rd refl (.n0 , refl) r1)
                | nat i | .(just n0) =
    deterministic hq r0 r1
  deterministic {l} {h0} {h1} {η} {wr[ x , y ],, e} hq
                (e-wr xq0 yq0 (n0 , nq0) r0) (e-wr xq1 yq1 (n1 , nq1) r1)
                with η x | η y
  deterministic {l} {h0} {h1} {η} {wr[ x , y ],, e} hq
                (e-wr refl refl (n0 , nq0) r0) (e-wr refl refl (n1 , nq1) r1)
                | nat i | nat n rewrite hq i with h1 i
  deterministic {l} {h0} {h1} {η} {wr[ x , y ],, e} hq
                (e-wr refl refl (n0 , refl) r0) (e-wr refl refl (.n0 , refl) r1)
                | nat i | nat n | .(just n0) =
    deterministic (write-ext i n hq) r0 r1
  deterministic hq (e-op xq0 yq0 r0) (e-op xq1 yq1 r1) rewrite xq0 | yq0 with tt
  deterministic hq (e-op xq0 yq0 r0) (e-op refl refl r1) | tt =
    deterministic hq r0 r1
  deterministic {l} {h0} {h1} {η} {let-app[ x , y ],, e} hq
                (e-app q0 r0′ r0) (e-app q1 r1′ r1)
                with η x
  deterministic {l} {h0} {h1} {η} {let-app[ x , y ],, e} hq
                (e-app refl r0′ r0) (e-app refl r1′ r1)
                | clo el ηl with deterministic hq r0′ r1′
  ... | hlq , refl = deterministic (sym ∘ hlq) r0 r1
  deterministic hq (e-lam r0) (e-lam r1) = deterministic hq r0 r1
  deterministic hq (e-val r0) (e-val r1) = deterministic hq r0 r1
  deterministic hq (e-var q0) (e-var q1) =
    (λ i → trans (sym (q0 i)) (trans (sym (hq i)) (q1 i))) , refl

  infix 4 _⊆_

  _⊆_ : (h h′ : Heap) → Set
  h ⊆ h′ = ∀ {i} → i ∈dom h → i ∈dom h′

  write-here : ∀ i n h → write i n h i ≡ just n
  write-here i n h with i ≟ i
  write-here i n h | yes _ = refl
  write-here i n h | no ¬q = ⊥-elim (¬q refl)

  write-there : ∀ i n h j → i ≢ j → write i n h j ≡ h j
  write-there i n h j ¬q with i ≟ j
  write-there i n h j ¬q | yes q = ⊥-elim (¬q q)
  write-there i n h j ¬q | no _ = refl

  ⊆-write : ∀ i n h → h ⊆ write i n h
  ⊆-write i n h {j} j∈ with i ≟ j
  ... | yes refl = n , refl
  ... | no ¬q = j∈

  ⊇-write : ∀ i n h → i ∈dom h → write i n h ⊆ h
  ⊇-write i n h d {j} j∈ with i ≟ j
  ... | yes refl = d
  ... | no ¬q = j∈

  dom-⊆ : ∀ {l h η} {e : Exp l} {h′ v} → h , η , e ⇓ h′ , v → h ⊆ h′
  dom-⊆ (e-if0-t q r) j∈ = dom-⊆ r j∈
  dom-⊆ (e-if0-f ¬q r) j∈ = dom-⊆ r j∈
  dom-⊆ (e-rd iq d r) j∈ = dom-⊆ r j∈
  dom-⊆ {h = h} (e-wr {i = i} {n} xq yq _ r) j∈ = dom-⊆ r (⊆-write i n h j∈)
  dom-⊆ (e-op xq yq r) j∈ = dom-⊆ r j∈
  dom-⊆ (e-app q r′ r) j∈ = dom-⊆ r (dom-⊆ r′ j∈)
  dom-⊆ (e-lam r) j∈ = dom-⊆ r j∈
  dom-⊆ (e-val r) j∈ = dom-⊆ r j∈
  dom-⊆ (e-var q) {j} j∈ rewrite q j = j∈

  dom-⊇ : ∀ {l h η} {e : Exp l} {h′ v} → h , η , e ⇓ h′ , v → h′ ⊆ h
  dom-⊇ (e-if0-t q r) j∈ = dom-⊇ r j∈
  dom-⊇ (e-if0-f ¬q r) j∈ = dom-⊇ r j∈
  dom-⊇ (e-rd iq d r) j∈ = dom-⊇ r j∈
  dom-⊇ {h = h} (e-wr {i = i} {n} xq yq i∈ r) {j} j∈ =
    ⊇-write i n h i∈ (dom-⊇ r j∈)
  dom-⊇ (e-op xq yq r) j∈ = dom-⊇ r j∈
  dom-⊇ (e-app q r′ r) j∈ = dom-⊇ r′ (dom-⊇ r j∈)
  dom-⊇ (e-lam r) j∈ = dom-⊇ r j∈
  dom-⊇ (e-val r) j∈ = dom-⊇ r j∈
  dom-⊇ (e-var q) {j} j∈ rewrite q j = j∈

  _#_ : (h h′ : Heap) → Set
  h # h′ = (∀ {i} → i ∈dom h → i ∉dom h′) × (∀ {i} → i ∈dom h′ → i ∉dom h)

  _∪_ : (h h′ : Heap) → Heap
  (h ∪ h′) i with h i
  ... | just n = just n
  ... | nothing = h′ i

  ⊆-refl : ∀ {h} → h ⊆ h
  ⊆-refl = id

  ⊆-∪ : (∀ {h h′} → h ⊆ h ∪ h′) × (∀ {h h′} → h′ ⊆ h ∪ h′)
  ⊆-∪ = (λ {h} {h′} → l h h′) , λ {h} {h′} → r h h′
    where
    l : ∀ h h′ → h ⊆ h ∪ h′
    l h h′ {i} (n , nq) with h i
    l h h′ {i} (n , refl) | .(just n) = n , refl

    r : ∀ h h′ → h′ ⊆ h ∪ h′
    r h h′ {i} i∈ with h i
    ... | just n = n , refl
    ... | nothing = i∈

  ⊇-preserves-# : ∀ {h h′ h0 h0′} → h′ ⊆ h → h0′ ⊆ h0 → h # h0 → h′ # h0′
  proj₁ (⊇-preserves-# {h} {h′} {h0} {h0′} hsub h0sub (h↛h0 , h0↛h)) {i} ∈h′ =
    ¬∈dom→∉dom {i} {h0′} (∉dom→¬∈dom {i} {h0} (h↛h0 (hsub ∈h′)) ∘ h0sub)
  proj₂ (⊇-preserves-# {h} {h′} {h0} {h0′} hsub h0sub (h↛h0 , h0↛h)) {i} ∈h0′ =
    ¬∈dom→∉dom {i} {h′} (∉dom→¬∈dom {i} {h} (h0↛h (h0sub ∈h0′)) ∘ hsub)

  ∈dom-prop : ∀ {i h} (x y : i ∈dom h) → x ≡ y
  ∈dom-prop {i} {h} (xn , xq) (yn , yq) with h i
  ∈dom-prop {i} {h} (xn , refl) (.xn , refl) | .(just xn) = refl

  write-∪ : ∀ i n h h0 → write i n h ∪ h0 ≗ write i n (h ∪ h0)
  write-∪ i n h h0 j with i ≟ j
  write-∪ i n h h0 .i | yes refl = refl
  write-∪ i n h h0 j | no ¬p with h j
  ... | just n″ = refl
  ... | nothing = refl

  local : ∀ {l h h′ h0 η v} {e : Exp l} → h # h0 →
          h , η , e ⇓ h′ , v → h ∪ h0 , η , e ⇓ h′ ∪ h0 , v
  local sep (e-if0-t q r) = e-if0-t q (local sep r)
  local sep (e-if0-f nq r) = e-if0-f nq (local sep r)
  local {h = h} {h′} {h0} sep (e-rd {i = i} q (n , hi≡jn) r) =
    e-rd q (n , eq) (local sep r)
    where
    eq : (h ∪ h0) i ≡ just n
    eq rewrite hi≡jn = refl
  local {h = h} {h′} {h0} {η} {v} sep (e-wr {e = e} {i = i} {n} xq yq i∈ r) =
    e-wr xq yq (proj₁ ⊆-∪ {h} {h0} i∈) lemma
    where
    ih : write i n h ∪ h0 , η , e ⇓ h′ ∪ h0 , v
    ih = local (⊇-preserves-# (⊇-write i n h i∈) id sep) r

    lemma : write i n (h ∪ h0) , η , e ⇓ h′ ∪ h0 , v
    lemma = ⇓-ext-h (write-∪ i n h h0) ih
  local sep (e-op xq yq r) = e-op xq yq (local sep r)
  local sep (e-app q r′ r) =
    e-app q (local sep r′) (local (⊇-preserves-# (dom-⊇ r′) id sep) r)
  local sep (e-lam r) = e-lam (local sep r)
  local sep (e-val r) = e-val (local sep r)
  local {l} {h} {h′} {h0} sep (e-var q) = e-var q′
    where
    q′ : h ∪ h0 ≗ h′ ∪ h0
    q′ i rewrite q i = refl
