{-

Defines fibration structures and fibrations.

-}
{-# OPTIONS --rewriting #-}
module fibration.fibration where

open import prelude
open import axioms

----------------------------------------------------------------------
-- Open boxes
----------------------------------------------------------------------

record OpenBox {ℓ} (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ → Set ℓ) : Set ℓ
  where
  constructor makeBox
  field
    cof : CofProp
    tube : [ cof ] → Π A
    cap : A r [ cof ↦ tube ◆ r ]

open OpenBox public

reshapeBox : ∀ {ℓ} {S T : Shape} (σ : ShapeHom S T)
  {r : ⟨ S ⟩} {A : ⟨ T ⟩ → Set ℓ}
  → OpenBox T (⟪ σ ⟫ r) A → OpenBox S r (A ∘ ⟪ σ ⟫)
reshapeBox σ box .cof = box .cof
reshapeBox σ box .tube = box .tube ◇ ⟪ σ ⟫
reshapeBox σ box .cap = box .cap

mapBox : ∀ {ℓ ℓ'} {S : Shape} {r : ⟨ S ⟩}
  {A : ⟨ S ⟩ → Set ℓ} {B : ⟨ S ⟩ → Set ℓ'}
  → (∀ s → A s → B s)
  → OpenBox S r A → OpenBox S r B
mapBox f box .cof = box .cof
mapBox f box .tube u i = f i (box .tube u i)
mapBox f box .cap .fst = f _ (box .cap .fst)
mapBox f box .cap .snd u = cong (f _) (box .cap .snd u)

abstract
  boxExt : ∀ {ℓ} {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Set ℓ}
    {box box' : OpenBox S r A}
    → box .cof ≡ box' .cof
    → (∀ u v → box .tube u ≡ box' .tube v)
    → box .cap .fst ≡ box' .cap .fst
    → box ≡ box'
  boxExt {box = box} refl q refl =
    congΣ (λ t c → makeBox (box .cof) t (box .cap .fst , c))
      (funext λ _ → q _ _)
      (funext λ _ → uipImp)

  boxExtDep : ∀ {ℓ ℓ'} (S : Shape) {B : Set ℓ} {A : B → ⟨ S ⟩ → Set ℓ'}
    {b₀ b₁ : B} (b : b₀ ≡ b₁)
    {r : ⟨ S ⟩}
    {box₀ : OpenBox S r (A b₀)} {box₁ : OpenBox S r (A b₁)}
    → box₀ .cof ≡ box₁ .cof
    → (∀ u v → subst (λ b' → Π (A b')) b (box₀ .tube u) ≡ box₁ .tube v)
    → subst (A ◆ r) b (box₀ .cap .fst) ≡ box₁ .cap .fst
    → subst (OpenBox S r ∘ A) b box₀ ≡ box₁
  boxExtDep S refl f r x = boxExt f r x

----------------------------------------------------------------------
-- Solutions to individual lifting problems
----------------------------------------------------------------------

record Filler {ℓ} (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ → Set ℓ) (box : OpenBox S r A) : Set ℓ
  where
  constructor makeFiller
  field
    fill : (s : ⟨ S ⟩) → A s [ box .cof ↦ box .tube ◆ s ]
    cap≡ : fill r .fst ≡ box .cap .fst

open Filler public

reshapeFiller : ∀ {ℓ} {S T : Shape} (σ : ShapeHom S T)
  {r : ⟨ S ⟩} {A : ⟨ T ⟩ → Set ℓ}
  {box : OpenBox T (⟪ σ ⟫ r) A}
  → Filler T (⟪ σ ⟫ r) A box
  → Filler S r (A ∘ ⟪ σ ⟫) (reshapeBox σ box)
reshapeFiller σ w .fill = w .fill ∘ ⟪ σ ⟫
reshapeFiller σ w .cap≡ = w .cap≡

abstract
  fillerExt : ∀ {ℓ} {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Set ℓ}
    {box : OpenBox S r A}
    {co co' : Filler S r A box}
    → (∀ s → co .fill s .fst ≡ co' .fill s .fst)
    → co ≡ co'
  fillerExt p =
    congΣ makeFiller
      (funext λ s → Σext (p s) (funext λ _ → uipImp))
      uipImp

  fillerCong : ∀ {ℓ} {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Set ℓ}
    {box : OpenBox S r A}
    {co co' : Filler S r A box}
    → co ≡ co'
    → (∀ s → co .fill s .fst ≡ co' .fill s .fst)
  fillerCong p s = cong fst (appCong (cong fill p))

----------------------------------------------------------------------
-- Equivariant fibrations
----------------------------------------------------------------------

record isFib {ℓ ℓ'} {Γ : Set ℓ} (A : Γ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor makeFib
  field
    lift : ∀ S r p box → Filler S r (A ∘ p) box
    vary : ∀ S T → (σ : ShapeHom S T) → ∀ r p box s
      → reshapeFiller σ (lift T (⟪ σ ⟫ r) p box) .fill s .fst
        ≡ lift S r (p ∘ ⟪ σ ⟫) (reshapeBox σ box) .fill s .fst

open isFib public

Fib : ∀ {ℓ} (ℓ' : Level) (Γ : Set ℓ) → Set (ℓ ⊔ lsuc ℓ')
Fib ℓ' Γ = Σ (Γ → Set ℓ') isFib

----------------------------------------------------------------------
-- Fibrations can be reindexed
----------------------------------------------------------------------

reindex : ∀{ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} (A : Γ → Set ℓ'')
  (α : isFib A) (ρ : Δ → Γ) → isFib (A ∘ ρ)
reindex A α ρ .lift S r p = α .lift S r (ρ ∘ p)
reindex A α ρ .vary S T σ r p = α .vary S T σ r (ρ ∘ p)

reindexFib : ∀{ℓ ℓ' ℓ''}{Δ : Set ℓ}{Γ : Set ℓ'}(Aα : Fib ℓ'' Γ)(ρ : Δ → Γ) → Fib ℓ'' Δ
reindexFib (A , α) ρ .fst = A ∘ ρ
reindexFib (A , α) ρ .snd = reindex A α ρ

reindexSubst : ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'} {A A' : Γ → Set ℓ''}
 (ρ : Δ → Γ)(P : A ≡ A') (Q : A ∘ ρ ≡ A' ∘ ρ) (α : isFib A)
  → reindex A' (subst isFib P α) ρ ≡ subst isFib Q (reindex A α ρ)
reindexSubst ρ refl refl α = refl

----------------------------------------------------------------------
-- Reindexing is functorial
----------------------------------------------------------------------

reindexAlongId : ∀{ℓ ℓ'} {Γ : Set ℓ}{A : Γ → Set ℓ'}{α : isFib A} → α ≡ reindex A α id
reindexAlongId = refl

reindexComp :
  ∀{ℓ ℓ' ℓ'' ℓ'''} {Γ₁ : Set ℓ} {Γ₂ : Set ℓ'} {Γ₃ : Set ℓ''} {A : Γ₃ → Set ℓ'''}
  {α : isFib A} (f : Γ₁ → Γ₂) (g : Γ₂ → Γ₃)
  → ----------------------
  reindex A α (g ∘ f) ≡ reindex (A ∘ g) (reindex A α g) f
reindexComp g f = refl

reindexAlongId' : ∀{ℓ ℓ'} {Γ : Set ℓ} {Aα : Fib ℓ' Γ} → reindexFib Aα id ≡ Aα
reindexAlongId' = refl

reindexComp' : ∀{ℓ ℓ' ℓ'' ℓ'''} {Γ₁ : Set ℓ} {Γ₂ : Set ℓ'} {Γ₃ : Set ℓ''}
  {Aα : Fib ℓ''' Γ₃}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindexFib Aα (g ∘ f) ≡ reindexFib (reindexFib Aα g) f
reindexComp' g f = refl

----------------------------------------------------------------------
-- An extensionality principle for fibration structures
----------------------------------------------------------------------
abstract
  isFibExt : ∀{ℓ ℓ'}{Γ : Set ℓ}{A : Γ → Set ℓ'}{α α' : isFib A} →
    ((S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → Γ) (box : OpenBox S r (A ∘ p))
      → (s : ⟨ S ⟩) → α .lift S r p box .fill s .fst ≡ α' .lift S r p box .fill s .fst)
    → α ≡ α'
  isFibExt q =
    congΣ makeFib
      (funext λ S → funext λ r → funext λ p → funext λ box → fillerExt (q S r p box))
      (funext λ S → funext λ T → funext λ σ → funext λ r → funext λ p → funext λ box → funext λ s →
        uipImp)

----------------------------------------------------------------------
-- Fibration structures can be transferred across isomorphisms
----------------------------------------------------------------------

_≅'_ : ∀{ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ') → Set (ℓ ⊔ ℓ')
_≅'_ {Γ = Γ} A B = (x : Γ) → A x ≅ B x

isomorphicIsFib : ∀{ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ') → (A ≅' B) → isFib B → isFib A
isomorphicIsFib A B iso β .lift S r p box = filler
  where
  fillerB = β .lift S r p (mapBox (to ∘ iso ∘ p) box)

  filler : Filler S r _ box
  filler .fill s .fst = iso (p s) .from (fillerB .fill s .fst)
  filler .fill s .snd u =
    symm (appCong (iso (p s) .inv₁))
    ∙ cong (iso (p s) .from) (fillerB .fill s .snd u)
  filler .cap≡ =
    cong (iso (p r) .from) (fillerB .cap≡)
    ∙ appCong (iso (p r) .inv₁)

isomorphicIsFib A B iso β .vary S T σ r p box s =
  cong (iso _ .from) (β .vary S T σ r p (mapBox (to ∘ iso ∘ p) box) s)
