{-

Tinyness of shapes.

-}
module axiom.tiny where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration

------------------------------------------------------------------------------------------
-- Each shape is tiny (exponentiation by it has a right adjoint).
------------------------------------------------------------------------------------------

_^_ : ∀ {ℓ} (Γ : Type ℓ) (S : Shape) → Type ℓ
Γ ^ S = ⟨ S ⟩ → Γ

_`^_ : ∀ {ℓ ℓ'} {Γ : Type ℓ} {Γ' : Type ℓ'}
  (ρ : Γ → Γ') (S : Shape) → (Γ ^ S → Γ' ^ S)
(ρ `^ S) = ρ ∘_

module Tiny (@♭ S : Shape) where

  postulate
    --↓ The right adjoint on objects.

    √ : ∀ {@♭ ℓ} (@♭ A : Type ℓ) → Type ℓ

  module _ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'} where

    postulate
      --↓ Right transposition across the adjunction.

      R : @♭ (A ^ S → B) → (A → √ B)

      --↓ Left transposition across the adjunction.

      L : @♭ (A → √ B) → (A ^ S → B)

      --↓ Right and left transposition are mutually inverse.

      LR : (@♭ f : (A ^ S) → B) → L (R f) ≡ f
      RL : (@♭ g : A → √ B) → R (L g) ≡ g

    {-# REWRITE LR RL #-}

  postulate
    --↓ One-sided naturality of right transposition.

    R℘ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
      (@♭ h : A → A') (@♭ f : A' ^ S → B)
      → R (f ∘ h `^ S) ≡ R f ∘ h

  --↓ One-sided naturality of left transposition is derivable.

  L℘ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
    (@♭ g : A' → √ B) (@♭ h : A → A')
    → L g ∘ (h `^ S) ≡ L (g ∘ h)
  L℘ g h = cong♭ L (R℘ h (L g))

  --↓ Functoriality of √ in the type argument.

  √` : ∀ {@♭ ℓ ℓ'}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ h : A → B) → √ A → √ B
  √` h = R (h ∘ L id)

  --↓ The other naturality property of right transposition.

  √R : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ f : (⟨ S ⟩ → A) → B)
    → √` h ∘ R f ≡ R (h ∘ f)
  √R {A = A} {B} {C = C} h f =
    sym (R℘ (R f) (h ∘ L id))
    ∙ cong♭ (λ f' → R (h ∘ f')) (L℘ id (R f))

  --↓ The other naturality property of left transposition.

  L√ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ B : Type ℓ'} {@♭ C : Type ℓ''}
    (@♭ h : B → C) (@♭ g : A → √ B)
    → h ∘ L g  ≡ L (√` h ∘ g)
  L√ h g = cong♭ L (sym (√R h (L g)))


  --↓ The right adjoint induces a dependent right adjoint
  --↓ TODO elaborate (including about universe level)

  opaque
    √ᴰ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ')
      → (Γ → Type (lsuc ℓ'))
    √ᴰ {ℓ} {ℓ'} B γ = Σ C ∈ √ (Type* ℓ') , √` fst C ≡ R B γ

  module _ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ B : Γ ^ S → Type ℓ') where

    opaque
      unfolding √ᴰ

      Rᴰ : @♭ (Γ ^ S ⊢ˣ B) → (Γ ⊢ˣ √ᴰ B)
      Rᴰ f γ .fst = R (B ,, f) γ
      Rᴰ f _ .snd = cong$ (√R fst (B ,, f))

      Lᴰ : @♭ (Γ ⊢ˣ √ᴰ B) → (Γ ^ S ⊢ˣ B)
      Lᴰ g p =
        coe
          (cong$ (L√ fst (fst ∘ g) ∙ cong♭ L (funExt (snd ∘ g))))
          (L (fst ∘ g) p .snd)

      LRᴰ : (@♭ f : Γ ^ S ⊢ˣ B) → Lᴰ (Rᴰ f) ≡ f
      LRᴰ f =
        funExt' $ adjustSubstEq id refl refl _ refl refl

      RLᴰ : (@♭ g : Γ ⊢ˣ √ᴰ B) → Rᴰ (Lᴰ g) ≡ g
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
      → ∀ γ → √ᴰ (B ∘ (ρ `^ S)) γ ≡ √ᴰ B (ρ γ)
    √ᴰ-reindex ρ B a =
      cong (λ T → Σ C ∈ √ (Type* _) , √` fst C ≡ T) (cong$ (R℘ ρ B))

    counitᴰ : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ}
      (@♭ B : Γ ^ S → Type ℓ') {p : Γ ^ S}
      → ((s : ⟨ S ⟩) → √ᴰ B (p s)) → B p
    counitᴰ B q =
      Lᴰ (B ∘ (fst `^ S)) (coe (sym (√ᴰ-reindex fst B _)) ∘ snd) (_ ,, q)

    √ᴰ` : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ}
      {@♭ B : Γ ^ S → Type ℓ'} {@♭ B' : Γ ^ S → Type ℓ''}
      (@♭ h : Γ ^ S ⊢ˣ B →ˣ B')
      → Γ ⊢ˣ √ᴰ B →ˣ √ᴰ B'
    √ᴰ` {B = B} {B' = B'} h γ √b =
      coe (√ᴰ-reindex fst B' (γ , √b)) $
      Rᴰ
        (λ p → B' (fst ∘ p))
        (λ p → h (fst ∘ p) (counitᴰ B (snd ∘ p)))
        (γ , √b)

    R℘ᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      {@♭ B : Γ' ^ S → Type ℓ''}
      (@♭ ρ : Γ → Γ')
      (@♭ f : Γ' ^ S ⊢ˣ B)
      (γ : Γ)
      → coe (√ᴰ-reindex ρ B γ) (Rᴰ (B ∘ (ρ `^ S)) (f ∘ (ρ `^ S)) γ) ≡ Rᴰ B f (ρ γ)
    R℘ᴰ {B = B} ρ f a =
      sym (substCongAssoc id (λ T → Σ C ∈ √ (Type* _) , √` fst C ≡ T) (cong$ (R℘ ρ B)) _)
      ∙ Σext
        (substNaturality (λ _ → fst) (cong$ (R℘ ρ B))
          ∙ substConst (cong$ (R℘ ρ B)) _
          ∙ cong$ (R℘ ρ (B ,, f)))
        uip'

    L℘ᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ Γ : Type ℓ} {@♭ Γ' : Type ℓ'}
      {@♭ B : Γ' ^ S → Type ℓ''}
      (@♭ g : Γ' ⊢ˣ √ᴰ B)
      (@♭ ρ : Γ → Γ')
      (p : Γ ^ S)
      → Lᴰ B g (ρ ∘ p) ≡ Lᴰ (B ∘ (ρ `^ S)) (coe (sym (√ᴰ-reindex ρ B _)) ∘ g ∘ ρ) p
    L℘ᴰ {B = B} g ρ p =
      cong$ $
      sym (LRᴰ (B ∘ (ρ `^ S)) (Lᴰ B g ∘ (ρ `^ S)))
      ∙ cong♭ (Lᴰ (B ∘ (ρ `^ S)))
        (funExt $ λ γ →
          adjustSubstEq id (√ᴰ-reindex ρ B γ) refl refl (sym (√ᴰ-reindex ρ B γ)) refl
          ∙ cong (coe (sym (√ᴰ-reindex ρ B γ))) (R℘ᴰ ρ (Lᴰ B g) γ ∙ cong$ (RLᴰ B g)))

    √Rᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ Γ : Type ℓ}
      {@♭ B : Γ ^ S → Type ℓ'}
      {@♭ B' : Γ ^ S → Type ℓ''}
      (@♭ h : Γ ^ S ⊢ˣ B →ˣ B')
      (@♭ f : Γ ^ S ⊢ˣ B)
      → appˣ (√ᴰ` h) (Rᴰ B f) ≡ Rᴰ B' (appˣ h f)
    √Rᴰ {B = B} {B'} h f =
      funExt λ γ →
      adjustSubstEq id refl _ _ refl
        (sym (R℘ᴰ (id ,, Rᴰ B f) (λ p → h (fst ∘ p) (counitᴰ B (snd ∘ p))) γ))
      ∙ cong♭
          (λ f' → Rᴰ B' (appˣ h f') γ)
          (funExt (L℘ᴰ (coe (sym (√ᴰ-reindex fst B _)) ∘ snd) (id ,, Rᴰ B f))
            ∙ cong♭ (Lᴰ B)
              (funExt λ γ →
                adjustSubstEq
                id
                refl
                (sym (√ᴰ-reindex fst B (γ , Rᴰ B f γ)))
                (sym (√ᴰ-reindex (id ,, Rᴰ B f) (B ∘ (fst `^ S)) γ))
                refl
                refl)
            ∙ LRᴰ B f)

    L√ᴰ : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Γ : Type ℓ}
      {@♭ B : Γ ^ S → Type ℓ'}
      {@♭ B' : Γ ^ S → Type ℓ''}
      (@♭ h : Γ ^ S ⊢ˣ B →ˣ B')
      (@♭ g : Γ ⊢ˣ √ᴰ B)
      → appˣ h (Lᴰ B g)  ≡ Lᴰ B' (appˣ (√ᴰ` h) g)
    L√ᴰ {B = B} {B' = B'} h g =
      sym (LRᴰ B' (appˣ h (Lᴰ B g))) ∙
      cong♭ (Lᴰ B') (sym (√Rᴰ h (Lᴰ B g)) ∙ cong (appˣ (√ᴰ` h)) (RLᴰ B g))

open Tiny

--↓ Functoriality and naturality in the shape argument.

module _ {@♭ S T : Shape} (@♭ σ : ShapeHom S T) where

  √ShapeHom : ∀ {@♭ ℓ} {@♭ A : Type ℓ}
    → √ S A → √ T A
  √ShapeHom = R T (L S id ∘ (_∘ ⟪ σ ⟫))

  LShapeHom : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ f : A → √ S B)
    → L T (√ShapeHom ∘ f) ≡ L S f ∘ (_∘ ⟪ σ ⟫)
  LShapeHom f =
    sym (L℘ T √ShapeHom f)
    ∙ cong (_∘ (_∘ ⟪ σ ⟫)) (L℘ S id f)

  ShapeHomR : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    (@♭ g : (⟨ S ⟩ → A) → B)
    → √ShapeHom ∘ R S g ≡ R T (g ∘ (_∘ ⟪ σ ⟫))
  ShapeHomR g =
    cong♭ (R T) (LShapeHom (R S g))
