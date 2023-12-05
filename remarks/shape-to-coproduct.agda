{-

  Derives from external tinyness of the shape S that dependent exponentation by
  S commutes with coproducts.

  This argument relies on the fact that the universe of crisp types is closed under coproducts.
  TODO elaborate

-}
{-# OPTIONS --rewriting #-}
module remarks.shape-to-coproduct where

open import prelude
open import axioms.funext
open import axioms.truncation
open import axioms.shape
open import axioms.cofibration
open import axioms.tiny

open Tiny

module _ (@♭ S : Shape) where

  shape→⊎♭ : ∀ {@♭ ℓ ℓ'} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
    → ((⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) ≅ (⟨ S ⟩ → A ⊎ B)
  shape→⊎♭ {A = A} {B} =
    record
    { to = forward
    ; from = L S back
    ; inv₁ = funExt back∘forward
    ; inv₂ = L√ S forward back ∙ cong♭ (L S) (funExt forward∘back)
    }
    where
    forward = [ inl ∘_ ∣ inr ∘_ ]
    back = [ R S inl ∣ R S inr ]

    forward∘back : (c : A ⊎ B) → √` S forward (back c) ≡ R S id c
    forward∘back (inl a) = appCong (√R S forward inl ∙ R℘ S inl id)
    forward∘back (inr b) = appCong (√R S forward inr ∙ R℘ S inr id)

    back∘forward : (d : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) → L S back (forward d) ≡ d
    back∘forward (inl f) = appCong (L℘ S back inl)
    back∘forward (inr g) = appCong (L℘ S back inr)

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

  shape→⊎ : ∀ {@♭ ℓ ℓ'}
    {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
    → ((s : ⟨ S ⟩) → A s ⊎ B s) → Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B
  shape→⊎ {ℓ} {ℓ'} {A} {B} h = main
    where
    Typeₗ = Σ AB ∈ Type ℓ × Type ℓ' , AB .fst
    Typeᵣ = Σ AB ∈ Type ℓ × Type ℓ' , AB .snd

    iso = shape→⊎♭

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
      ∙ cong (iso .from) (shape→⊎♭` fst fst (iso .from h'))
      ∙ cong (iso .from ∘ ((fst ⊎` fst) ∘_)) (appCong (iso .inv₂))

    baseEq : ∇ (((fst ∘_) ⊎` (fst ∘_)) (shape→⊎♭ .from h')) ≡ AB
    baseEq =
      cong ∇ fromNatural
      ∙ sym (shape→⊎♭∇ (iso .from ((fst ⊎` fst) ∘ h')))
      ∙ cong (∇ ∘_) (appCong (iso .inv₂))
      ∙ funExt fsth'

    main : Π ⟨ S ⟩ A ⊎ Π ⟨ S ⟩ B
    main with shape→⊎♭ .from h' | baseEq
    main | inl f | eq = inl λ s → subst fst (appCong eq) (f s .snd)
    main | inr g | eq = inr λ s → subst snd (appCong eq) (g s .snd)
