{-

  Derives from external tinyness of the shape S that dependent exponentation by
  S commutes with coproducts.

  This argument relies on the fact that the universe of crisp types is closed under coproducts.
  TODO elaborate

-}
module shape-to-coproduct where

open import prelude
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration
open import axiom.tiny

module _ (@♭ S : Shape) where

  open Tiny S

  shape→⊎♭ : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    → ((⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) ≅ (⟨ S ⟩ → A ⊎ B)
  shape→⊎♭ {A = A} {B} =
    record
    { to = forward
    ; from = L back
    ; inv₁ = funExt back∘forward
    ; inv₂ = L√ forward back ∙ cong♭ L (funExt forward∘back)
    }
    where
    forward = [ inl ∘_ ∣ inr ∘_ ]
    back = [ R inl ∣ R inr ]

    forward∘back : (c : A ⊎ B) → √` forward (back c) ≡ R id c
    forward∘back (inl a) = appCong (√R forward inl ∙ R℘ inl id)
    forward∘back (inr b) = appCong (√R forward inr ∙ R℘ inr id)

    back∘forward : (d : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) → L back (forward d) ≡ d
    back∘forward (inl f) = appCong (L℘ back inl)
    back∘forward (inr g) = appCong (L℘ back inr)

  shape→⊎♭` : ∀ {@♭ ℓ ℓ' ℓ'' ℓ'''}
      {@♭ A : Type ℓ} {@♭ A' : Type ℓ'}
      {@♭ B : Type ℓ''} {@♭ B' : Type ℓ'''}
      (f : A → A') (g : B → B')
      (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B))
      → shape→⊎♭ .to (((f ∘_) ⊎` (g ∘_)) p) ≡ (f ⊎` g) ∘ (shape→⊎♭ .to p)
  shape→⊎♭` f g (inl _) = refl
  shape→⊎♭` f g (inr _) = refl

  shape→⊎♭∇ : ∀ {@♭ ℓ} {@♭ A : Type ℓ}
    (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → A))
    → ∇ ∘ shape→⊎♭ .to p ≡ ∇ p
  shape→⊎♭∇ (inl _) = refl
  shape→⊎♭∇ (inr _) = refl

shape→⊎ : ∀ {@♭ ℓ ℓ'} (S : Shape)
  {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
  → ((s : ⟨ S ⟩) → A s ⊎ B s) → Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B
shape→⊎ {ℓ} {ℓ'} = ShapeIsDiscrete main
  where
  module _ (@♭ S : Shape) {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
    (h : (s : ⟨ S ⟩) → A s ⊎ B s)
    where

    Ctx = Type ℓ × Type ℓ'
    Typeₗ = Σ AB ∈ Ctx , AB .fst
    Typeᵣ = Σ AB ∈ Ctx , AB .snd

    addCtx : (s : ⟨ S ⟩) → A s ⊎ B s → Typeₗ ⊎ Typeᵣ
    addCtx s = (A s , B s ,_) ⊎` (A s , B s ,_)

    getCtx : Typeₗ ⊎ Typeᵣ → Ctx
    getCtx = ∇ ∘ fst ⊎` fst

    iso♭ = shape→⊎♭ S

    h' : ⟨ S ⟩ → Typeₗ ⊎ Typeᵣ
    h' s = addCtx s (h s)

    getAddTypes : ∀ s c → getCtx (addCtx s c) ≡ (A s , B s)
    getAddTypes s = ⊎-elim (λ _ → refl) (λ _ → refl)

    fromNatural : ((fst ∘_) ⊎` (fst ∘_)) (iso♭ .from h') ≡ iso♭ .from ((fst ⊎` fst) ∘ h')
    fromNatural =
      sym (appCong (iso♭ .inv₁))
      ∙ cong (iso♭ .from) (shape→⊎♭` S fst fst (iso♭ .from h'))
      ∙ cong (iso♭ .from ∘ ((fst ⊎` fst) ∘_)) (appCong (iso♭ .inv₂))

    typesEq : ∇ (((fst ∘_) ⊎` (fst ∘_)) (iso♭ .from h')) ≡ (A ,, B)
    typesEq =
      cong ∇ fromNatural
      ∙ sym (shape→⊎♭∇ S (iso♭ .from ((fst ⊎` fst) ∘ h')))
      ∙ cong (∇ ∘_) (appCong (iso♭ .inv₂))
      ∙ funExt (λ s → getAddTypes s (h s))

    main : Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B
    main =
      ⊎-elim
        {C = λ c → ∇ (((fst ∘_) ⊎` (fst ∘_)) c) ≡ (A ,, B) → Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B}
        (λ f eq → inl λ s → subst fst (appCong eq) (f s .snd))
        (λ g eq → inr λ s → subst snd (appCong eq) (g s .snd))
        (iso♭ .from h')
        typesEq
