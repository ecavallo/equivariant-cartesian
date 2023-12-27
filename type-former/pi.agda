{-

Fibration structure on Π-types.

-}
module type-former.pi where

open import prelude
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration
open import fibration.coercion

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

Πˣ : (A : Γ → Type ℓ) (B : Γ ▷ˣ A → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
Πˣ A B γ = (a : A γ) → B (γ , a)

_→ˣ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
A →ˣ B = Πˣ A (B ∘ 𝒑)

λˣ : {A : Γ → Type ℓ} {B : Γ ▷ˣ A → Type ℓ'}
  → Γ ▷ˣ A ⊢ˣ B
  → Γ ⊢ˣ Πˣ A B
λˣ f γ a = f (γ , a)

appˣ : {A : Γ → Type ℓ} {B : Γ ▷ˣ A → Type ℓ'}
  → (f : Γ ⊢ˣ Πˣ A B) (a : Γ ⊢ˣ A)
  → Γ ⊢ˣ B ∘ (id ,, a)
appˣ f a γ = f γ (a γ)

module ΠLift {S r}
  {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ S ⟩ ▷ˣ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox S r (Πˣ A B))
  where

  module _ (s : ⟨ S ⟩) (a : A s) where

    module Dom = Coerce S s (A , α) a

    module _ (coerceA : (i : ⟨ S ⟩) → A i) where

      boxCod : OpenBox S r (B ∘ (id ,, coerceA))
      boxCod = mapBox (λ i f → f (coerceA i)) box

      fillCod = β .lift S r (id ,, coerceA) boxCod

  filler : Filler box
  filler .fill s .out a =
    subst (curry B s)
      (Dom.cap≡ s a)
      (fillCod s a (Dom.coerce s a) .fill s .out)
  filler .fill s .out≡ u =
    funExt λ a →
    sym (congdep (box .tube s u) (Dom.cap≡ s a))
    ∙ cong (subst (curry B s) (Dom.cap≡ s a))
        (fillCod s a (Dom.coerce s a) .fill s .out≡ u)
  filler .cap≡ =
    funExt λ a →
    cong (subst (curry B r) (Dom.cap≡ r a))
      (fillCod r a (Dom.coerce r a) .cap≡)
    ∙ congdep (box .cap .out) (Dom.cap≡ r a)

module ΠVary {S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ T ⟩ ▷ˣ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox T (⟪ σ ⟫ r) (Πˣ A B))
  where

  module T = ΠLift α β box
  module S = ΠLift (α ∘ᶠˢ ⟪ σ ⟫) (β ∘ᶠˢ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  varyDom : ∀ s a i → T.Dom.coerce (⟪ σ ⟫ s) a (⟪ σ ⟫ i) ≡ S.Dom.coerce s a i
  varyDom s = coerceVary σ s (A , α)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    funExt λ a →
    cong
      (subst (curry B (⟪ σ ⟫ s)) (T.Dom.cap≡ _ a))
      (β .vary S T σ r (id ,, T.Dom.coerce _ a) (T.boxCod _ a (T.Dom.coerce _ a)) s)
    ∙
    adjustSubstEq (curry B (⟪ σ ⟫ s))
      (cong$ (funExt (varyDom s a))) refl
      (T.Dom.cap≡ (⟪ σ ⟫ s) a) (S.Dom.cap≡ s a)
      (sym (substCongAssoc (curry B (⟪ σ ⟫ s)) (λ cA → cA s) (funExt (varyDom s a)) _)
        ∙ congdep (λ cA → S.fillCod s a cA .fill s .out) (funExt (varyDom s a)))

opaque
  ΠFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ ▷ˣ A → Type ℓ'} (β : FibStr B)
    → FibStr (Πˣ A B)
  ΠFibStr α β .lift S r p = ΠLift.filler (α ∘ᶠˢ p) (β ∘ᶠˢ (p ×id))
  ΠFibStr α β .vary S T σ r p = ΠVary.eq σ (α ∘ᶠˢ p) (β ∘ᶠˢ (p ×id))

  ----------------------------------------------------------------------------------------
  -- Forming Π-types is stable under reindexing
  ----------------------------------------------------------------------------------------

  reindexΠFibStr : {A : Γ → Type ℓ} {α : FibStr A} {B : Γ ▷ˣ A → Type ℓ'} {β : FibStr B}
    (ρ : Δ → Γ) → ΠFibStr α β ∘ᶠˢ ρ ≡ ΠFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ (ρ ×id))
  reindexΠFibStr ρ = FibStrExt λ _ _ _ _ _ → refl

Πᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ') → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Πᶠ A B .fst = Πˣ (A .fst) (B .fst)
Πᶠ A B .snd = ΠFibStr (A .snd) (B .snd)

reindexΠᶠ : {A : Γ ⊢ᶠType ℓ} {B : Γ ▷ᶠ A ⊢ᶠType ℓ'}
  (ρ : Δ → Γ) → Πᶠ A B ∘ᶠ ρ ≡ Πᶠ (A ∘ᶠ ρ) (B ∘ᶠ (ρ ×id))
reindexΠᶠ ρ = Σext refl (reindexΠFibStr ρ)

_→ᶠ_ : (A : Γ ⊢ᶠType ℓ) (B : Γ ⊢ᶠType ℓ') → Γ ⊢ᶠType (ℓ ⊔ ℓ')
A →ᶠ B = Πᶠ A (B ∘ᶠ 𝒑)
