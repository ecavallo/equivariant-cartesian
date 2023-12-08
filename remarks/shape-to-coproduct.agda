{-

  Derives from external tinyness of the shape S that dependent exponentation by
  S commutes with coproducts.

  This argument relies on the fact that the universe of crisp types is closed under coproducts.
  TODO elaborate

  TODO move out of "remarks"

-}
module remarks.shape-to-coproduct where

open import prelude
open import axioms.funext
open import axioms.truncation
open import axioms.shape
open import axioms.cofibration
open import axioms.tiny

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

    Typeₗ = Σ AB ∈ Type ℓ × Type ℓ' , AB .fst
    Typeᵣ = Σ AB ∈ Type ℓ × Type ℓ' , AB .snd

    iso = shape→⊎♭ S

    AB : ⟨ S ⟩ → Type ℓ × Type ℓ'
    AB s = (A s , B s)

    h' : ⟨ S ⟩ → Typeₗ ⊎ Typeᵣ
    h' s = ((_,_ (AB s)) ⊎` (_,_ (AB s))) (h s)

    fsth' : ∀ s → ∇ ((fst ⊎` fst) (h' s)) ≡ AB s
    fsth' s with h s
    fsth' s | inl _ = refl
    fsth' s | inr _ = refl

    fromNatural : ((fst ∘_) ⊎` (fst ∘_)) (iso .from h') ≡ iso .from ((fst ⊎` fst) ∘ h')
    fromNatural =
      sym (appCong (iso .inv₁))
      ∙ cong (iso .from) (shape→⊎♭` S fst fst (iso .from h'))
      ∙ cong (iso .from ∘ ((fst ⊎` fst) ∘_)) (appCong (iso .inv₂))

    baseEq : ∇ (((fst ∘_) ⊎` (fst ∘_)) (shape→⊎♭ S .from h')) ≡ AB
    baseEq =
      cong ∇ fromNatural
      ∙ sym (shape→⊎♭∇ S (iso .from ((fst ⊎` fst) ∘ h')))
      ∙ cong (∇ ∘_) (appCong (iso .inv₂))
      ∙ funExt fsth'

    main : Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B
    main with iso .from h' | baseEq
    main | inl f | eq = inl λ s → subst fst (appCong eq) (f s .snd)
    main | inr g | eq = inr λ s → subst snd (appCong eq) (g s .snd)
