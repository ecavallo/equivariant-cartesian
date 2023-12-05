{-

Fibration structure on Π-types.

-}
module type-formers.pi where

open import prelude
open import axioms
open import fibration.fibration
open import fibration.coercion

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

Πᴵ : (A : Γ → Type ℓ) (B : Γ ▷ A → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
Πᴵ A B x = (a : A x) → B (x , a)

_→ᴵ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
A →ᴵ B = Πᴵ A (B ∘ fst)

module ΠLift {S r}
  {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ S ⟩ ▷ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox S r (Πᴵ A B))
  where

  module _ (s : ⟨ S ⟩) (a : A s) where

    module C = Coerce S s (A , α) a

    module _ (coerceA : (i : ⟨ S ⟩) → A i) where

      boxB : OpenBox S r (B ∘ (id ,, coerceA))
      boxB = mapBox (λ i f → f (coerceA i)) box

      fillB = β .lift S r (id ,, coerceA) boxB

  filler : Filler box
  filler .fill s .out a =
    subst (curry B s)
      (C.cap≡ s a)
      (fillB s a (C.coerce s a) .fill s .out)
  filler .fill s .out≡ u =
    funExt λ a →
    sym (congdep (box .tube s u) (C.cap≡ s a))
    ∙ cong (subst (curry B s) (C.cap≡ s a))
        (fillB s a (C.coerce s a) .fill s .out≡ u)
  filler .cap≡ =
    funExt λ a →
    cong (subst (curry B r) (C.cap≡ r a))
      (fillB r a (C.coerce r a) .cap≡)
    ∙ congdep (box .cap .out) (C.cap≡ r a)

module ΠVary {S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ T ⟩ ▷ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox T (⟪ σ ⟫ r) (Πᴵ A B))
  where

  module T = ΠLift α β box
  module S =
    ΠLift (α ∘ᶠˢ ⟪ σ ⟫) (β ∘ᶠˢ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  varyA : ∀ s a i → T.C.coerce (⟪ σ ⟫ s) a (⟪ σ ⟫ i) ≡ S.C.coerce s a i
  varyA s = coerceVary σ s (A , α)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    funExt λ a →
    cong
      (subst (curry B (⟪ σ ⟫ s)) (T.C.cap≡ _ a))
      (β .vary S T σ r (id ,, T.C.coerce _ a) (T.boxB _ a (T.C.coerce _ a)) s)
    ∙
    adjustSubstEq (curry B (⟪ σ ⟫ s))
      (appCong (funExt (varyA s a))) refl
      (T.C.cap≡ (⟪ σ ⟫ s) a) (S.C.cap≡ s a)
      (sym (substCongAssoc (curry B (⟪ σ ⟫ s)) (λ cA → cA s) (funExt (varyA s a)) _)
        ∙ congdep (λ cA → S.fillB s a cA .fill s .out) (funExt (varyA s a)))

opaque
  ΠFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ ▷ A → Type ℓ'} (β : FibStr B)
    → FibStr (Πᴵ A B)
  ΠFibStr α β .lift S r p = ΠLift.filler (α ∘ᶠˢ p) (β ∘ᶠˢ (p ×id))
  ΠFibStr α β .vary S T σ r p = ΠVary.eq σ (α ∘ᶠˢ p) (β ∘ᶠˢ (p ×id))

  ----------------------------------------------------------------------------------------
  -- Forming Π-types is stable under reindexing
  ----------------------------------------------------------------------------------------

  reindexΠFibStr : {A : Γ → Type ℓ} {α : FibStr A} {B : Γ ▷ A → Type ℓ'} {β : FibStr B}
    (ρ : Δ → Γ) → ΠFibStr α β ∘ᶠˢ ρ ≡ ΠFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ (ρ ×id))
  reindexΠFibStr ρ = FibStrExt λ _ _ _ _ _ → refl

Πᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ') → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Πᶠ A B .fst = Πᴵ (A .fst) (B .fst)
Πᶠ A B .snd = ΠFibStr (A .snd) (B .snd)

reindexΠᶠ : {A : Γ ⊢ᶠType ℓ} {B : Γ ▷ᶠ A ⊢ᶠType ℓ'}
  (ρ : Δ → Γ) → Πᶠ A B ∘ᶠ ρ ≡ Πᶠ (A ∘ᶠ ρ) (B ∘ᶠ (ρ ×id))
reindexΠᶠ ρ = Σext refl (reindexΠFibStr ρ)

_→ᶠ_ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') → Γ ⊢ᶠType (ℓ ⊔ ℓ')
A →ᶠ B = Πᶠ A (B ∘ᶠ fst)
