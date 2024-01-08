{-

Tinyness of shapes.

-}
module tiny where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration
open import axiom.tiny

infixr 4 _√ᴰ_

module Tiny (@♭ S : Shape) where

  open √Axioms S public

  --↓ One-sided naturality of left transposition is derivable.

  L^ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
    (@♭ g : A' → S √ B) (@♭ h : A → A')
    → L g ∘ (h `^ S) ≡ L (g ∘ h)
  L^ g h = cong♭ L (R^ h (L g))

  --↓ Functoriality of √ in the type argument.

  √` : ∀ {@♭ ℓ ℓ'}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ h : A → B) → S √ A → S √ B
  √` h = R (h ∘ L id)

  --↓ The other naturality property of right transposition.

  √R : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ f : (⟨ S ⟩ → A) → B)
    → √` h ∘ R f ≡ R (h ∘ f)
  √R {A = A} {B} {C = C} h f =
    sym (R^ (R f) (h ∘ L id))
    ∙ cong♭ (λ f' → R (h ∘ f')) (L^ id (R f))

  --↓ The other naturality property of left transposition.

  L√ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ g : A → S √ B)
    → h ∘ L g  ≡ L (√` h ∘ g)
  L√ h g = cong♭ L (sym (√R h (L g)))

--↓ The right adjoint induces a dependent right adjoint
--↓ TODO elaborate (including about universe level)

opaque
  _√ᴰ_ : ∀ {@♭ ℓ ℓ'} (@♭ S : Shape) {@♭ Γ : Type ℓ}
    (@♭ B : Γ ^ S → Type ℓ')
    → (Γ → Type (lsuc ℓ'))
  (S √ᴰ B) γ = Σ C ∈ S √ (Type* _) , √` fst C ≡ R B γ
    where
    open Tiny S

module DependentTiny (@♭ S : Shape) where

  open Tiny S

  module _ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ B : Γ ^ S → Type ℓ') where

    opaque
      unfolding _√ᴰ_

      Rᴰ : @♭ (Γ ^ S ⊢ˣ B) → (Γ ⊢ˣ S √ᴰ B)
      Rᴰ f γ .fst = R (B ,, f) γ
      Rᴰ f _ .snd = cong$ (√R fst (B ,, f))

      Lᴰ : @♭ (Γ ⊢ˣ S √ᴰ B) → (Γ ^ S ⊢ˣ B)
      Lᴰ g p =
        coe
          (cong$ (L√ fst (fst ∘ g) ∙ cong♭ L (funExt (snd ∘ g))))
          (L (fst ∘ g) p .snd)

      LRᴰ : (@♭ f : Γ ^ S ⊢ˣ B) → Lᴰ (Rᴰ f) ≡ f
      LRᴰ f =
        funExt' $ adjustSubstEq id refl refl _ refl refl

      RLᴰ : (@♭ g : Γ ⊢ˣ S √ᴰ B) → Rᴰ (Lᴰ g) ≡ g
      RLᴰ g =
        funExt' $ Σext (cong$ (cong♭ R (sym lemma))) uip'
        where
        lemma : L (fst ∘ g) ≡ (B ,, Lᴰ g)
        lemma = funExt' $ Σext _ refl

  opaque
    unfolding Rᴰ Lᴰ

    √ᴰ-reindex : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      (@♭ ρ : Γ → Γ')
      (@♭ B : Γ' ^ S → Type ℓ'')
      → ∀ γ → (S √ᴰ B) (ρ γ) ≡ (S √ᴰ B ∘ (ρ `^ S)) γ
    √ᴰ-reindex ρ B _ =
      cong (λ T → Σ C ∈ S √ (Type* _) , √` fst C ≡ T) (cong$ (sym (R^ ρ B)))

  √ᴰ-reindex-compute : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    (@♭ ρ : Γ → Γ')
    {@♭ B : Γ' ^ S → Type ℓ''}
    → Γ ⊢ˣ (S √ᴰ B) ∘ ρ →ˣ S √ᴰ (B ∘ (ρ `^ S))
  √ᴰ-reindex-compute ρ {B = B} γ = coe (√ᴰ-reindex ρ B γ)

  √ᴰ-reindex-expand : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    (@♭ ρ : Γ → Γ')
    {@♭ B : Γ' ^ S → Type ℓ''}
    → Γ ⊢ˣ S √ᴰ (B ∘ (ρ `^ S)) →ˣ (S √ᴰ B) ∘ ρ
  √ᴰ-reindex-expand ρ {B = B} γ = coe (sym (√ᴰ-reindex ρ B γ))

  √ᴰ-reindex-compute-∘ : ∀ {@♭ ℓ ℓ' ℓ'' ℓ'''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} {@♭ Γ'' : Type ℓ''}
    (@♭ ρ' : Γ' → Γ'') (@♭ ρ : Γ → Γ')
    {@♭ B : Γ'' ^ S → Type ℓ'''}
    (b : Γ ⊢ˣ (S √ᴰ B) ∘ ρ' ∘ ρ)
    → appˣ (√ᴰ-reindex-compute ρ) (appˣ (√ᴰ-reindex-compute ρ' ∘ ρ) b)
      ≡ appˣ (√ᴰ-reindex-compute (ρ' ∘ ρ)) b
  √ᴰ-reindex-compute-∘ ρ' ρ {B = B} b =
    funExt λ γ →
    adjustSubstEq
      id
      refl
      (√ᴰ-reindex ρ' B (ρ γ))
      (√ᴰ-reindex ρ (B ∘ (ρ' `^ S)) γ)
      (√ᴰ-reindex (ρ' ∘ ρ) B γ)
      refl

  √ᴰ-reindex-expand-∘ : ∀ {@♭ ℓ ℓ' ℓ'' ℓ'''}
    {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'} {@♭ Γ'' : Type ℓ''}
    (@♭ ρ' : Γ' → Γ'') (@♭ ρ : Γ → Γ')
    {@♭ B : Γ'' ^ S → Type ℓ'''}
    (b : Γ ⊢ˣ S √ᴰ (B ∘ (ρ' ∘ ρ) `^ S))
    → appˣ (√ᴰ-reindex-expand ρ' ∘ ρ) (appˣ (√ᴰ-reindex-expand ρ) b)
      ≡ appˣ (√ᴰ-reindex-expand (ρ' ∘ ρ)) b
  √ᴰ-reindex-expand-∘ ρ' ρ {B = B} b =
    funExt λ γ →
    adjustSubstEq
      id
      refl
      (sym (√ᴰ-reindex ρ (B ∘ (ρ' `^ S)) γ))
      (sym (√ᴰ-reindex ρ' B (ρ γ)))
      (sym (√ᴰ-reindex (ρ' ∘ ρ) B γ))
      refl

  √ᴰ-reindex-compute-expand : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    (@♭ ρ : Γ → Γ')
    {@♭ B : Γ' ^ S → Type ℓ''}
    (b : Γ ⊢ˣ S √ᴰ (B ∘ (ρ `^ S)))
    → appˣ (√ᴰ-reindex-compute ρ {B}) (appˣ (√ᴰ-reindex-expand ρ) b) ≡ b
  √ᴰ-reindex-compute-expand ρ {B} b =
    funExt λ γ → adjustSubstEq id refl _ (√ᴰ-reindex ρ B γ) refl refl

  √ᴰ-reindex-expand-compute : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
    (@♭ ρ : Γ → Γ')
    {@♭ B : Γ' ^ S → Type ℓ''}
    (b : Γ ⊢ˣ (S √ᴰ B) ∘ ρ)
    → appˣ (√ᴰ-reindex-expand ρ {B}) (appˣ (√ᴰ-reindex-compute ρ) b) ≡ b
  √ᴰ-reindex-expand-compute ρ {B} b =
    funExt λ γ → adjustSubstEq id refl _ (sym (√ᴰ-reindex ρ B γ)) refl refl

  opaque
    unfolding Rᴰ Lᴰ √ᴰ-reindex

    R^ᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      {@♭ B : Γ' ^ S → Type ℓ''}
      (@♭ ρ : Γ → Γ')
      (@♭ f : Γ' ^ S ⊢ˣ B)
      → appˣ (√ᴰ-reindex-compute ρ) (Rᴰ B f ∘ ρ) ≡ Rᴰ (B ∘ (ρ `^ S)) (f ∘ (ρ `^ S))
    R^ᴰ {B = B} ρ f =
      funExt λ γ →
      sym (substCongAssoc id (λ T → Σ C ∈ _ , √` fst C ≡ T) (cong$ (sym (R^ ρ B))) _)
      ∙ Σext
        (substNaturality fst (cong$ (sym (R^ ρ B)))
          ∙ substConst (cong$ (sym (R^ ρ B))) _
          ∙ cong$ (sym (R^ ρ (B ,, f))))
        uip'

  opaque
    unfolding √ᴰ-reindex

    L^ᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      {@♭ B : Γ' ^ S → Type ℓ''}
      (@♭ g : Γ' ⊢ˣ S √ᴰ B)
      (@♭ ρ : Γ → Γ')
      → Lᴰ B g ∘ (ρ `^ S) ≡ Lᴰ (B ∘ (ρ `^ S)) (appˣ (√ᴰ-reindex-compute ρ) (g ∘ ρ))
    L^ᴰ {B = B} g ρ =
      sym (LRᴰ (B ∘ (ρ `^ S)) (Lᴰ B g ∘ (ρ `^ S)))
      ∙ cong♭ (Lᴰ (B ∘ (ρ `^ S)))
        (sym (R^ᴰ ρ (Lᴰ B g)) ∙ cong (appˣ (√ᴰ-reindex-compute ρ)) (cong (_∘ ρ) (RLᴰ B g)))

  opaque
    inᴰ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ^ S → Type ℓ'}
      → @♭ (Γ ^ S ⊢ˣ B)
      → (Γ ⊢ˣ S √ᴰ B)
    inᴰ = Rᴰ _

    outᴰ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ▷⟨ S ⟩ ^ S → Type ℓ'}
      → @♭ (Γ ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
      → Γ ⊢ˣ B ∘ ^-η S
    outᴰ t = Lᴰ _ t ∘ ^-η S

    out-inᴰ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : (Γ ▷⟨ S ⟩) ^ S → Type ℓ'}
      (@♭ b : Γ ▷⟨ S ⟩ ^ S ⊢ˣ B)
      → outᴰ (inᴰ b) ≡ b ∘ ^-η S
    out-inᴰ b = cong (_∘ ^-η S) (LRᴰ _ b)

    in-outᴰ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} {@♭ B : Γ ^ S → Type ℓ'}
      (@♭ t : Γ ⊢ˣ S √ᴰ B)
      → t ≡ inᴰ (outᴰ (appˣ (√ᴰ-reindex-compute (^-ε S)) (t ∘ ^-ε S)))
    in-outᴰ t =
      sym (RLᴰ _ t) ∙ cong♭ (Rᴰ _) (cong (_∘ ^-η S) (L^ᴰ t (^-ε S)))

    inᴰ-reindex : ∀ {@♭ ℓ ℓ' ℓ''}
        {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
        {@♭ B : Γ' ^ S → Type ℓ''}
        (@♭ ρ : Γ → Γ')
        (@♭ f : Γ' ^ S ⊢ˣ B)
        → appˣ (√ᴰ-reindex-compute ρ) (inᴰ f ∘ ρ) ≡ inᴰ (f ∘ (ρ `^ S))
    inᴰ-reindex = R^ᴰ

    outᴰ-reindex : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      {@♭ B : Γ' ▷⟨ S ⟩ ^ S → Type ℓ''}
      (@♭ ρ : Γ → Γ')
      (@♭ t : Γ' ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
      → outᴰ t ∘ ρ ≡ outᴰ (appˣ (√ᴰ-reindex-compute (ρ ×id)) (t ∘ ρ ×id))
    outᴰ-reindex ρ t =
      cong (_∘ ^-η S) (L^ᴰ t (ρ ×id))

  opaque
    √ᴰ` : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ}
      {@♭ B : Γ ^ S → Type ℓ'} {@♭ B' : Γ ^ S → Type ℓ''}
      (@♭ h : Γ ^ S ⊢ˣ B →ˣ B')
      → @♭ (Γ ⊢ˣ S √ᴰ B)
      → Γ ⊢ˣ S √ᴰ B'
    √ᴰ` h t =
      inᴰ $♭
      appˣ h $
      outᴰ $♭
      appˣ (√ᴰ-reindex-compute (^-ε S)) $
      t ∘ ^-ε S

    √-inᴰ : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ}
        {@♭ B : Γ ^ S → Type ℓ'} {@♭ B' : Γ ^ S → Type ℓ''}
        (@♭ h : Γ ^ S ⊢ˣ B →ˣ B')
        (@♭ b : Γ ^ S ⊢ˣ B)
        → √ᴰ` h (inᴰ b) ≡ inᴰ (appˣ h b)
    √-inᴰ h b =
      cong♭ (λ t → inᴰ $♭ appˣ h $ outᴰ $♭ t) (inᴰ-reindex _ b)
      ∙ cong♭ (λ b' → inᴰ $♭ appˣ h b') (out-inᴰ _)

    out-√ᴰ : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ}
        {@♭ B : Γ ▷⟨ S ⟩ ^ S → Type ℓ'} {@♭ B' : Γ ▷⟨ S ⟩ ^ S → Type ℓ''}
        (@♭ h : Γ ▷⟨ S ⟩ ^ S ⊢ˣ B →ˣ B')
        (@♭ t : Γ ▷⟨ S ⟩ ⊢ˣ S √ᴰ B)
        → outᴰ (√ᴰ` h t) ≡ appˣ (h ∘ ^-η S) (outᴰ t)
    out-√ᴰ h t =
      out-inᴰ _
      ∙ cong (appˣ (h ∘ ^-η S))
          (outᴰ-reindex (^-η S) _
            ∙ cong♭ (outᴰ) (√ᴰ-reindex-compute-∘ (^-ε S) (^-η S ×id) t)
            ∙ sym (outᴰ-reindex _ t))

  opaque
    √ᴰPreservesProp : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → @♭ ((@♭ b b' : Γ ^ S ⊢ˣ B) → b ≡ b')
      → ((@♭ t t' : Γ ⊢ˣ S √ᴰ B) → t ≡ t')
    √ᴰPreservesProp B propB t t' =
      in-outᴰ t ∙ cong♭ inᴰ (propB _ _) ∙ sym (in-outᴰ t')

    √ᴰPreservesProp' : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → @♭ (∀ p (b b' : B p) → b ≡ b')
      → ∀ γ (t t' : (S √ᴰ B) γ) → t ≡ t'
    √ᴰPreservesProp' {Γ = Γ} B propB γ t t' =
      cong$ {a = γ , (t , t')} lem''
      where
      lem : ((@♭ t t' : Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B) ⊢ˣ S √ᴰ (B ∘ (𝒑 `^ S))) → t ≡ t')
      lem =
        √ᴰPreservesProp
          {Γ = Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B)}
          (B ∘ (𝒑 `^ S))
          (λ b b' → funExt λ p → propB (𝒑 ∘ p) (b p) (b' p))

      lem' :
        _≡_
          {A = Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B) ⊢ˣ S √ᴰ (B ∘ (𝒑 `^ S))}
          (appˣ (√ᴰ-reindex-compute 𝒑) (fstˣ 𝒒))
          (appˣ (√ᴰ-reindex-compute 𝒑) (sndˣ 𝒒))
      lem' =
        lem (appˣ (√ᴰ-reindex-compute 𝒑) (fstˣ 𝒒)) (appˣ (√ᴰ-reindex-compute 𝒑) (sndˣ 𝒒))

      lem'' :
        _≡_
          {A = Γ ▷ˣ (S √ᴰ B ×ˣ S √ᴰ B) ⊢ˣ (S √ᴰ B) ∘ 𝒑}
          (fstˣ 𝒒)
          (sndˣ 𝒒)
      lem'' =
        sym (√ᴰ-reindex-expand-compute 𝒑 (fstˣ 𝒒))
        ∙ cong (appˣ (√ᴰ-reindex-expand 𝒑)) lem'
        ∙ √ᴰ-reindex-expand-compute 𝒑 (sndˣ 𝒒)
