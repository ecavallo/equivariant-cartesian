{-

Fibration structure on Π-types.

-}
module type-former.pi where

open import basic
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration
open import fibration.transport

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

module ΠLift {S r}
  {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ S ⟩ ▷ˣ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox S (Πˣ A B) r)
  where

  module Dom = TranspStr (fibStrToTranspStr α)

  module _ (s : ⟨ S ⟩) (a : A s) (coerceA : (i : ⟨ S ⟩) → A i) where

      boxCod : OpenBox S (B ∘ (id ,, coerceA)) r
      boxCod = mapBox (λ {i} f → f (coerceA i)) box

      fillCod = β .lift S (id ,, coerceA) r boxCod

  filler : Filler box
  filler .fill s .out a =
    subst (curry B s)
      (Dom.cap≡ S id s a)
      (fillCod s a (Dom.lift S id s a) .fill s .out)
  filler .fill s .out≡ u =
    funExt λ a →
    sym (congdep (box .tube s u) (Dom.cap≡ S id s a))
    ∙ cong (subst (curry B s) (Dom.cap≡ S id s a))
        (fillCod s a (Dom.lift S id s a) .fill s .out≡ u)
  filler .cap≡ =
    funExt λ a →
    cong (subst (curry B r) (Dom.cap≡ S id r a))
      (fillCod r a (Dom.lift S id r a) .cap≡)
    ∙ congdep (box .cap .out) (Dom.cap≡ S id r a)

module ΠVary {S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ T ⟩ ▷ˣ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox T (Πˣ A B) (⟪ σ ⟫ r))
  where

  module T = ΠLift α β box
  module S = ΠLift (α ∘ᶠˢ ⟪ σ ⟫) (β ∘ᶠˢ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  varyDom : ∀ s a i → T.Dom.lift T id (⟪ σ ⟫ s) a (⟪ σ ⟫ i) ≡ S.Dom.lift S id s a i
  varyDom s = T.Dom.vary S T σ id s

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    funExt λ a →
    cong
      (subst (curry B (⟪ σ ⟫ s)) (T.Dom.cap≡ T id _ a))
      (β .vary S T σ (id ,, T.Dom.lift T id _ a) r (T.boxCod _ a (T.Dom.lift T id _ a)) s)
    ∙
    adjustSubstEq (curry B (⟪ σ ⟫ s))
      (cong$ (funExt (varyDom s a))) refl
      (T.Dom.cap≡ T id (⟪ σ ⟫ s) a) (S.Dom.cap≡ S id s a)
      (sym (substCongAssoc (curry B (⟪ σ ⟫ s)) (λ cA → cA s) (funExt (varyDom s a)) _)
        ∙ congdep (λ cA → S.fillCod s a cA .fill s .out) (funExt (varyDom s a)))

opaque
  ΠFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ ▷ˣ A → Type ℓ'} (β : FibStr B)
    → FibStr (Πˣ A B)
  ΠFibStr α β .lift S γ r = ΠLift.filler (α ∘ᶠˢ γ) (β ∘ᶠˢ (γ ×id))
  ΠFibStr α β .vary S T σ γ r = ΠVary.eq σ (α ∘ᶠˢ γ) (β ∘ᶠˢ (γ ×id))

--↓ Forming Π-types is stable under reindexing

opaque
  unfolding ΠFibStr
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
