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

module Tiny (@♭ S : Shape) where

  postulate
    --↓ The right adjoint on objects.

    √ : ∀ {@♭ ℓ} (@♭ A : Type ℓ) → Type ℓ

  module _ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'} where

    postulate
      --↓ Right transposition across the adjunction.

      R : @♭ ((⟨ S ⟩ → A) → B) → (A → √ B)

      --↓ Left transposition across the adjunction.

      L : @♭ (A → √ B) → ((⟨ S ⟩ → A) → B)

      --↓ Right and left transposition are mutually inverse.

      LR : (@♭ f : (⟨ S ⟩ → A) → B) → L (R f) ≡ f
      RL : (@♭ g : A → √ B) → R (L g) ≡ g

    {-# REWRITE LR RL #-}

  postulate
    --↓ One-sided naturality of right transposition.

    R℘ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
      (@♭ h : A → A') (@♭ f : (⟨ S ⟩ → A') → B)
      → R (f ∘ (h ∘_)) ≡ R f ∘ h

  --↓ One-sided naturality of left transposition is derivable.

  L℘ : ∀ {@♭ ℓ ℓ' ℓ''}
    {@♭ A : Type ℓ} {@♭ A' : Type ℓ'} {@♭ B : Type ℓ''}
    (@♭ g : A' → √ B) (@♭ h : A → A')
    → L g ∘ (h ∘_) ≡ L (g ∘ h)
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
    √ᴰ : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ}
      (@♭ B : (⟨ S ⟩ → A) → Type ℓ')
      → (A → Type (lsuc ℓ'))
    √ᴰ {ℓ} {ℓ'} B a = Σ C ∈ √ (Type* ℓ') , √` fst C ≡ R B a

  module _ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} (@♭ B : (⟨ S ⟩ → A) → Type ℓ') where

    opaque
      unfolding √ᴰ

      Rᴰ : @♭ ((p : ⟨ S ⟩ → A) → B p) → ((a : A) → √ᴰ B a)
      Rᴰ f a .fst = R (B ,, f) a
      Rᴰ f a .snd = cong$ (√R fst (B ,, f))

      Lᴰ : @♭ ((a : A) → √ᴰ B a) → ((p : ⟨ S ⟩ → A) → B p)
      Lᴰ g p =
        coe
          (cong$ (L√ fst (fst ∘ g) ∙ cong♭ L (funExt (snd ∘ g))))
          (L (fst ∘ g) p .snd)

      LRᴰ : (@♭ f : (p : ⟨ S ⟩ → A) → B p) → Lᴰ (Rᴰ f) ≡ f
      LRᴰ f =
        funExt' $ adjustSubstEq id refl refl _ refl refl

      RLᴰ : (@♭ g : (a : A) → √ᴰ B a) → Rᴰ (Lᴰ g) ≡ g
      RLᴰ g =
        funExt λ a →
        Σext (cong$ (cong♭ R (sym lemma))) uip'
        where
        lemma : L (fst ∘ g) ≡ (B ,, Lᴰ g)
        lemma = funExt' $ Σext _ refl

  opaque
    unfolding Rᴰ Lᴰ

    √ᴰ-reindex : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ A : Type ℓ} {@♭ A' : Type ℓ'}
      (@♭ h : A → A')
      (@♭ B : (⟨ S ⟩ → A') → Type ℓ'')
      → ∀ a → √ᴰ (B ∘ (h ∘_)) a ≡ √ᴰ B (h a)
    √ᴰ-reindex h B a =
      cong (λ T → Σ C ∈ √ (Type* _) , √` fst C ≡ T) (cong$ (R℘ h B))

    counitᴰ : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ}
      (@♭ B : (⟨ S ⟩ → A) → Type ℓ') {p : ⟨ S ⟩ → A}
      → ((s : ⟨ S ⟩) → √ᴰ B (p s)) → B p
    counitᴰ B q =
      Lᴰ (B ∘ (fst ∘_)) (coe (sym (√ᴰ-reindex fst B _)) ∘ snd) (_ ,, q)

    √ᴰ` : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ A : Type ℓ}
      {@♭ B : (⟨ S ⟩ → A) → Type ℓ'}
      {@♭ B' : (⟨ S ⟩ → A) → Type ℓ''}
      (@♭ h : ∀ p → B p → B' p)
      → ∀ a → √ᴰ B a → √ᴰ B' a
    √ᴰ` {B = B} {B' = B'} h a √b =
      coe (√ᴰ-reindex fst B' (a , √b)) $
      Rᴰ
        (λ p → B' (fst ∘ p))
        (λ p → h (fst ∘ p) (counitᴰ B (snd ∘ p)))
        (a , √b)

    R℘ᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ} {@♭ A' : Type ℓ'}
      {@♭ B : (⟨ S ⟩ → A') → Type ℓ''}
      (@♭ h : A → A')
      (@♭ f : (p : (⟨ S ⟩ → A')) → B p)
      (a : A)
      → coe (√ᴰ-reindex h B a) (Rᴰ (B ∘ (h ∘_)) (f ∘ (h ∘_)) a) ≡ Rᴰ B f (h a)
    R℘ᴰ {A' = A'} {B = B} h f a =
      sym (substCongAssoc id (λ T → Σ C ∈ √ (Type* _) , √` fst C ≡ T) (cong$ (R℘ h B)) _)
      ∙ Σext
        (substNaturality (λ _ → fst) (cong$ (R℘ h B))
          ∙ substConst (cong$ (R℘ h B)) _
          ∙ cong$ (R℘ h (B ,, f)))
        uip'

    L℘ᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ} {@♭ A' : Type ℓ'}
      {@♭ B : (⟨ S ⟩ → A') → Type ℓ''}
      (@♭ g : (a : A') → √ᴰ B a)
      (@♭ h : A → A')
      (p : ⟨ S ⟩ → A)
      → Lᴰ B g (h ∘ p) ≡ Lᴰ (B ∘ (h ∘_)) (λ a → coe (sym (√ᴰ-reindex h B a)) (g (h a))) p
    L℘ᴰ {B = B} g h p =
      cong$ $
      sym (LRᴰ (B ∘ (h ∘_)) (Lᴰ B g ∘ (h ∘_)))
      ∙ cong♭ (Lᴰ (B ∘ (h ∘_)))
        (funExt $ λ a →
          adjustSubstEq id (√ᴰ-reindex h B a) refl refl (sym (√ᴰ-reindex h B a)) refl
          ∙ cong (coe (sym (√ᴰ-reindex h B a))) (R℘ᴰ h (Lᴰ B g) a ∙ cong$ (RLᴰ B g)))

    √Rᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ}
      {@♭ B : (⟨ S ⟩ → A) → Type ℓ'}
      {@♭ B' : (⟨ S ⟩ → A) → Type ℓ''}
      (@♭ h : ∀ p → B p → B' p)
      (@♭ f : (p : (⟨ S ⟩ → A)) → B p)
      → √ᴰ` h _ ∘ Rᴰ B f ≡ Rᴰ B' (h _ ∘ f)
    √Rᴰ {A = A} {B} {B'} h f =
      funExt λ a →
      adjustSubstEq id refl _ _ refl
        (sym (R℘ᴰ (id ,, Rᴰ B f) (λ p → h (fst ∘ p) (counitᴰ B (snd ∘ p))) a))
      ∙ cong♭
          (λ f' → Rᴰ B' (h _ ∘ f') a)
          (funExt (L℘ᴰ (coe (sym (√ᴰ-reindex fst B _)) ∘ snd) (id ,, Rᴰ B f))
            ∙ cong♭ (Lᴰ B)
              (funExt λ a →
                adjustSubstEq
                id
                refl
                (sym (√ᴰ-reindex fst B (a , Rᴰ B f a)))
                (sym (√ᴰ-reindex (id ,, Rᴰ B f) (B ∘ (fst ∘_)) a))
                refl
                refl)
            ∙ LRᴰ B f)

    L√ᴰ : ∀ {@♭ ℓ ℓ' ℓ''}
      {@♭ A : Type ℓ}
      {@♭ B : (⟨ S ⟩ → A) → Type ℓ'}
      {@♭ B' : (⟨ S ⟩ → A) → Type ℓ''}
      (@♭ h : ∀ p → B p → B' p)
      (@♭ g : (a : A) → √ᴰ B a)
      → h _ ∘ Lᴰ B g  ≡ Lᴰ B' (√ᴰ` h _ ∘ g)
    L√ᴰ {B = B} {B' = B'} h g =
      sym (LRᴰ B' (h _ ∘ Lᴰ B g)) ∙
      cong♭ (Lᴰ B') (sym (√Rᴰ h (Lᴰ B g)) ∙ cong (√ᴰ` h _ ∘_) (RLᴰ B g))

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
