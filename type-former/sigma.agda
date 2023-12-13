{-

Fibration structure on Σ-types.

-}
module type-former.sigma where

open import prelude
open import internal-extensional-type-theory
open import axiom
open import cofibration
open import fibration.fibration

infixl 3 _,ᴵ_
infixr 3 _×ᴵ_

private variable
  ℓ ℓ' : Level
  Γ Δ : Type ℓ

Σᴵ : (A : Γ → Type ℓ) (B : Γ ▷ A → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
Σᴵ A B x = Σ a ∈ A x , B (x , a)

_×ᴵ_ : (A : Γ → Type ℓ) (B : Γ → Type ℓ') → Γ → Type (ℓ ⊔ ℓ')
(A ×ᴵ B) x = A x × B x

_,ᴵ_ : {A : Γ → Type ℓ} {B : Γ ▷ A → Type ℓ'}
  (a : Γ ⊢ A) → Γ ⊢ B ∘ (id ,, a) → Γ ⊢ Σᴵ A B
(a ,ᴵ b) γ .fst = a γ
(a ,ᴵ b) γ .snd = b γ

fstᴵ : {A : Γ → Type ℓ} {B : Γ ▷ A → Type ℓ'}
  → Γ ⊢ Σᴵ A B → Γ ⊢ A
fstᴵ = fst ∘_

sndᴵ : {A : Γ → Type ℓ} {B : Γ ▷ A → Type ℓ'}
  (t : Γ ⊢ Σᴵ A B) → Γ ⊢ B ∘ (id ,, fstᴵ t)
sndᴵ = snd ∘_

module ΣLift {S r}
  {A : ⟨ S ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ S ⟩ ▷ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox S r (Σᴵ A B))
  where

  boxFst : OpenBox S r A
  boxFst = mapBox (λ _ → fst) box

  fillFst = α .lift S r id boxFst

  module _ (cA : Filler boxFst) where

    boxSnd : OpenBox S r (B ∘ (id ,, out ∘ cA .fill))
    boxSnd .cof = box .cof
    boxSnd .tube i u = subst (curry B i) (cA .fill i .out≡ u) (box .tube i u .snd)
    boxSnd .cap .out = subst (curry B r) (sym (cA .cap≡)) (box .cap .out .snd)
    boxSnd .cap .out≡ u =
      adjustSubstEq (curry B r)
        (cong fst (box .cap .out≡ u)) refl
        (cA .fill r .out≡ u) (sym (cA .cap≡))
        (sym (substCongAssoc (curry B r) fst (box .cap .out≡ u) _)
          ∙ congdep snd (box .cap .out≡ u))

    fillSnd = β .lift S r (id ,, out ∘ cA .fill) boxSnd

  filler : Filler box
  filler .fill s .out .fst = fillFst .fill s .out
  filler .fill s .out .snd = fillSnd fillFst .fill s .out
  filler .fill s .out≡ u =
    Σext (fillFst .fill s .out≡ u) (fillSnd fillFst .fill s .out≡ u)
  filler .cap≡ =
    Σext (fillFst .cap≡)
      (adjustSubstEq (curry B r)
        refl (sym (fillFst .cap≡))
        (fillFst .cap≡) refl
        (fillSnd fillFst .cap≡))

module ΣVary {S T} (σ : ShapeHom S T) {r}
  {A : ⟨ T ⟩ → Type ℓ} (α : FibStr A)
  {B : ⟨ T ⟩ ▷ A → Type ℓ'} (β : FibStr B)
  (box : OpenBox T (⟪ σ ⟫ r) (Σᴵ A B))
  where

  module T = ΣLift α β box
  module S =
    ΣLift (α ∘ᶠˢ ⟪ σ ⟫) (β ∘ᶠˢ (⟪ σ ⟫ ×id)) (reshapeBox σ box)

  varyFst : reshapeFiller σ T.fillFst ≡ S.fillFst
  varyFst = fillerExt (α .vary S T σ r id T.boxFst)

  eq : (s : ⟨ S ⟩) → T.filler .fill (⟪ σ ⟫ s) .out ≡ S.filler .fill s .out
  eq s =
    Σext
      (α .vary S T σ r id T.boxFst s)
      (adjustSubstEq (curry B (⟪ σ ⟫ s))
         refl refl
         (α .vary S T σ r id T.boxFst s)
         (cong (λ cA → cA .fill s .out) varyFst)
         (β .vary S T σ r (id ,, out ∘ T.fillFst .fill) (T.boxSnd T.fillFst) s)
       ∙ sym (substCongAssoc (curry B (⟪ σ ⟫ s)) (λ cA → cA .fill s .out) varyFst _)
       ∙ congdep (λ cA → S.fillSnd cA .fill s .out) varyFst)

opaque
  ΣFibStr : {A : Γ → Type ℓ} (α : FibStr A) {B : Γ ▷ A → Type ℓ'} (β : FibStr B)
    → FibStr (Σᴵ A B)
  ΣFibStr α β .lift S r p = ΣLift.filler (α ∘ᶠˢ p) (β ∘ᶠˢ (p ×id))
  ΣFibStr α β .vary S T σ r p = ΣVary.eq σ (α ∘ᶠˢ p) (β ∘ᶠˢ (p ×id))

  ----------------------------------------------------------------------------------------
  -- Forming Σ-types is stable under reindexing
  ----------------------------------------------------------------------------------------

  reindexΣFibStr : {A : Γ → Type ℓ} {α : FibStr A} {B : Γ ▷ A → Type ℓ'} {β : FibStr B}
    (ρ : Δ → Γ) → ΣFibStr α β ∘ᶠˢ ρ ≡ ΣFibStr (α ∘ᶠˢ ρ) (β ∘ᶠˢ (ρ ×id))
  reindexΣFibStr ρ = FibStrExt λ _ _ _ _ _ → refl

Σᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ') → Γ ⊢ᶠType (ℓ ⊔ ℓ')
Σᶠ A B .fst = Σᴵ (A .fst) (B .fst)
Σᶠ A B .snd = ΣFibStr (A .snd) (B .snd)

reindexΣᶠ : {A : Γ ⊢ᶠType ℓ} {B : Γ ▷ᶠ A ⊢ᶠType ℓ'}
  (ρ : Δ → Γ) → Σᶠ A B ∘ᶠ ρ ≡ Σᶠ (A ∘ᶠ ρ) (B ∘ᶠ ρ ×id)
reindexΣᶠ ρ = Σext refl (reindexΣFibStr ρ)

pairᶠ : (A : Γ ⊢ᶠType ℓ) (B : Γ ▷ᶠ A ⊢ᶠType ℓ')
  (a : Γ ⊢ᶠ A)
  (b : Γ ⊢ᶠ B ∘ᶠ (id ,, a))
  → Γ ⊢ᶠ Σᶠ A B
pairᶠ A B = _,ᴵ_
