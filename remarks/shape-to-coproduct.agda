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
open import axioms.cofprop
open import axioms.tiny

open Tiny

module _ (@♭ S : Shape) where

  shape→⊎♭ : ∀ {@♭ ℓ ℓ'} {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    → ((⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) ≅ (⟨ S ⟩ → A ⊎ B)
  shape→⊎♭ {A = A} {B} =
    record
    { to = forward
    ; from = L S back
    ; inv₁ = funext back∘forward
    ; inv₂ = trans (cong♭ (L S) (funext forward∘back)) (L√ S forward back)
    }
    where
    forward = [ inl ∘_ ∣ inr ∘_ ]
    back = [ R S inl ∣ R S inr ]

    forward∘back : (c : A ⊎ B) → √` S forward (back c) ≡ R S id c
    forward∘back (inl a) = appCong (trans (R℘ S inl id) (√R S forward inl))
    forward∘back (inr b) = appCong (trans (R℘ S inr id) (√R S forward inr))

    back∘forward : (d : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B)) → L S back (forward d) ≡ d
    back∘forward (inl f) = appCong (L℘ S back inl)
    back∘forward (inr g) = appCong (L℘ S back inr)

  shape→⊎♭` : ∀ {@♭ ℓ ℓ' ℓ'' ℓ'''}
      {@♭ A : Set ℓ} {@♭ A' : Set ℓ'}
      {@♭ B : Set ℓ''} {@♭ B' : Set ℓ'''}
      (f : A → A') (g : B → B')
      (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → B))
      → shape→⊎♭ .to (((f ∘_) ⊎` (g ∘_)) p) ≡ (f ⊎` g) ∘ (shape→⊎♭ .to p)
  shape→⊎♭` f g (inl _) = refl
  shape→⊎♭` f g (inr _) = refl

  shape→⊎♭∇ : ∀ {@♭ ℓ} {@♭ A : Set ℓ}
    (p : (⟨ S ⟩ → A) ⊎ (⟨ S ⟩ → A))
    → ∇ ∘ shape→⊎♭ .to p ≡ ∇ p
  shape→⊎♭∇ (inl _) = refl
  shape→⊎♭∇ (inr _) = refl

  shape→⊎ : ∀ {@♭ ℓ ℓ'}
    {A : ⟨ S ⟩ → Set ℓ} {B : ⟨ S ⟩ → Set ℓ'}
    → ((s : ⟨ S ⟩) → A s ⊎ B s) → Π A ⊎ Π B
  shape→⊎ {ℓ} {ℓ'} {A} {B} h = main
    where
    Setₗ = Σ AB ∈ Set ℓ × Set ℓ' , AB .fst
    Setᵣ = Σ AB ∈ Set ℓ × Set ℓ' , AB .snd

    iso = shape→⊎♭

    AB : ⟨ S ⟩ → Set ℓ × Set ℓ'
    AB s = (A s , B s)

    h' : ⟨ S ⟩ → Setₗ ⊎ Setᵣ
    h' s = ((_,_ (AB s)) ⊎` (_,_ (AB s))) (h s)

    fsth' : ∀ s → ∇ ((fst ⊎` fst) (h' s)) ≡ AB s
    fsth' s with h s
    fsth' s | inl _ = refl
    fsth' s | inr _ = refl

    fromNatural : ((fst ∘_) ⊎` (fst ∘_)) (iso .from h') ≡ iso .from ((fst ⊎` fst) ∘ h')
    fromNatural =
      trans
        (trans
          (cong (iso .from ∘ ((fst ⊎` fst) ∘_)) (appCong (iso .inv₂)))
          (cong (iso .from) (shape→⊎♭` fst fst (iso .from h'))))
        (sym (appCong (iso .inv₁)))

    baseEq : ∇ (((fst ∘_) ⊎` (fst ∘_)) (shape→⊎♭ .from h')) ≡ AB
    baseEq =
      trans
        (trans
          (trans
            (funext fsth')
            (cong (∇ ∘_) (appCong (iso .inv₂))))
          (sym (shape→⊎♭∇ (iso .from ((fst ⊎` fst) ∘ h')))))
        (cong ∇ fromNatural)

    main : Π A ⊎ Π B
    main with shape→⊎♭ .from h' | baseEq
    main | inl f | eq = inl λ s → subst fst (appCong eq) (f s .snd)
    main | inr g | eq = inr λ s → subst snd (appCong eq) (g s .snd)
