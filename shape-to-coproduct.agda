{-

  Derives from external tinyness of the shape S that dependent exponentation by
  S commutes with coproducts.

  This argument relies on the fact that the universe of crisp types is closed under coproducts.
  TODO elaborate

-}
module shape-to-coproduct where

open import basic
open import internal-extensional-type-theory
open import axiom.funext
open import axiom.shape
open import axiom.cofibration
open import tiny

module _ (@♭ S : Shape) where

  open Tiny S

  shape→⊎♭ : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    → ((A ^ S) ⊎ (B ^ S)) ≅ ((A ⊎ B) ^ S)
  shape→⊎♭ {A = A} {B = B} = main
    where
    forward = [ inl `^ S ∣ inr `^ S ]
    back = [ transposeRight inl ∣ transposeRight inr ]

    forward∘back : ∀ c → √` forward (back c) ≡ transposeRight id c
    forward∘back (inl a) =
      cong$ (√TransposeRight forward inl ∙ transposeRight^ inl id)
    forward∘back (inr b) =
      cong$ (√TransposeRight forward inr ∙ transposeRight^ inr id)

    back∘forward : ∀ d → transposeLeft back (forward d) ≡ d
    back∘forward (inl f) = cong$ (transposeLeft^ back inl)
    back∘forward (inr g) = cong$ (transposeLeft^ back inr)

    main : ((A ^ S) ⊎ (B ^ S)) ≅ ((A ⊎ B) ^ S)
    main .to = forward
    main .from = transposeLeft back
    main .inv₁ = back∘forward
    main .inv₂ _ =
      cong$ (√TransposeLeft forward back ∙ cong♭ transposeLeft (funExt forward∘back))

  shape→⊎♭` : ∀ {@♭ ℓ ℓ' ℓ'' ℓ'''}
    {@♭ A : Type ℓ} {@♭ A' : Type ℓ'}
    {@♭ B : Type ℓ''} {@♭ B' : Type ℓ'''}
    (f : A → A') (g : B → B')
    (p : (A ^ S) ⊎ (B ^ S))
    → shape→⊎♭ .to (((f ∘_) ⊎` (g ∘_)) p) ≡ (f ⊎` g) ∘ (shape→⊎♭ .to p)
  shape→⊎♭` f g (inl _) = refl
  shape→⊎♭` f g (inr _) = refl

  shape→⊎♭∇ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → A))
    → ∇ ∘ shape→⊎♭ .to p ≡ ∇ p
  shape→⊎♭∇ (inl _) = refl
  shape→⊎♭∇ (inr _) = refl

shape→⊎ : ∀ {@♭ ℓ ℓ'} (S : Shape)
  {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
  → Π ⟨ S ⟩ (A ⊎ˣ B)
  → Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B
shape→⊎ {ℓ} {ℓ'} =
  ShapeIsDiscrete main
  where
  module _ (@♭ S : Shape)
    {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
    (h : Π ⟨ S ⟩ (A ⊎ˣ B))
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
      sym (iso♭ .inv₁ _)
      ∙ cong (iso♭ .from) (shape→⊎♭` S fst fst (iso♭ .from h'))
      ∙ cong (iso♭ .from ∘ ((fst ⊎` fst) ∘_)) (iso♭ .inv₂ _)

    typesEq : ∇ (((fst ∘_) ⊎` (fst ∘_)) (iso♭ .from h')) ≡ (A ,, B)
    typesEq =
      cong ∇ fromNatural
      ∙ sym (shape→⊎♭∇ S (iso♭ .from ((fst ⊎` fst) ∘ h')))
      ∙ cong (∇ ∘_) (iso♭ .inv₂ _)
      ∙ funExt (λ s → getAddTypes s (h s))

    main : Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B
    main =
      ⊎-elim
        {C = λ c → ∇ (((fst ∘_) ⊎` (fst ∘_)) c) ≡ (A ,, B) → Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B}
        (λ f eq → inl λ s → subst fst (cong$ eq) (f s .snd))
        (λ g eq → inr λ s → subst snd (cong$ eq) (g s .snd))
        (iso♭ .from h')
        typesEq
