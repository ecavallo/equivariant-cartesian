{-

Definition of composition and fibrations.

-}
{-# OPTIONS --rewriting #-}
module fibration.fibration where

open import prelude
open import axioms

----------------------------------------------------------------------
-- Composition structure
----------------------------------------------------------------------

record Comp {ℓ} (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ → Set ℓ)
  (φ : CofProp) (f : [ φ ] → Π A) (x₀ : A r [ φ ↦ f ◆ r ]) : Set ℓ
  where
  field
    comp : (s : ⟨ S ⟩) → A s [ φ ↦ f ◆ s ]
    cap : comp r .fst ≡ x₀ .fst

open Comp public

reshapeComp : ∀ {ℓ} {S T : Shape} (σ : ShapeHom S T)
  → ∀ {r} → {A : ⟨ T ⟩ → Set ℓ} → ∀ {φ f x₀}
  → Comp T (⟪ σ ⟫ r) A φ f x₀
  → Comp S r (A ∘ ⟪ σ ⟫) φ (f ◇ ⟪ σ ⟫) x₀
reshapeComp σ w .comp = w .comp ∘ ⟪ σ ⟫
reshapeComp σ w .cap = w .cap

abstract
  compExt : ∀ {ℓ} {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Set ℓ}
    {φ : CofProp} {f : [ φ ] → Π A} {x₀ : A r [ φ ↦ f ◆ r ]}
    {co co' : Comp S r A φ f x₀}
    → (∀ s → co .comp s .fst ≡ co' .comp s .fst)
    → co ≡ co'
  compExt p =
    cong
      (λ {(co , ca) → record {comp = co; cap = ca}})
      (Σext (funext λ s → Σext (p s) (funext λ _ → uipImp)) uipImp)

----------------------------------------------------------------------
-- Fibrations
----------------------------------------------------------------------
record isFib {ℓ ℓ'} {Γ : Set ℓ} (A : Γ → Set ℓ') : Set (ℓ ⊔ ℓ') where
  field
    lift : ∀ S r p φ f x₀ → Comp S r (A ∘ p) φ f x₀
    vary : ∀ S T → (σ : ShapeHom S T) → ∀ r p φ f x₀ s
      → lift T (⟪ σ ⟫ r) p φ f x₀ .comp (⟪ σ ⟫ s) .fst
        ≡ lift S r (p ∘ ⟪ σ ⟫) φ (f ◇ ⟪ σ ⟫) x₀ .comp s .fst

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
    ((S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → Γ) (φ : CofProp)
    (f : [ φ ] → Π (A ∘ p)) (x₀ : A (p r) [ φ ↦ f ◆ r ])
      → (s : ⟨ S ⟩) → α .lift S r p φ f x₀ .comp s .fst ≡ α' .lift S r p φ f x₀ .comp s .fst)
    → α ≡ α'
  isFibExt {Γ = Γ} {A} {α} {α'} q =
    cong
      (λ {(l , u) → record {lift = l; vary = u}})
      (Σext
        (funext λ S → funext λ r → funext λ p → funext λ φ → funext λ f → funext λ x₀ →
          compExt (q S r p φ f x₀))
        (funext λ S → funext λ T → funext λ σ → funext λ r → funext λ p →
          funext λ φ → funext λ f → funext λ x₀ → funext λ s →
            uipImp))

----------------------------------------------------------------------
-- Fibration structures can be transferred across isomorphisms
----------------------------------------------------------------------

_≅'_ : ∀{ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ') → Set (ℓ ⊔ ℓ')
_≅'_ {Γ = Γ} A B = (x : Γ) → A x ≅ B x

isomorphicIsFib : ∀{ℓ ℓ'} {Γ : Set ℓ} (A B : Γ → Set ℓ') → (A ≅' B) → isFib B → isFib A
isomorphicIsFib A B iso β .lift S r p φ f (a₀ , ex) = rec
  where
  tube : [ φ ] → Π (B ∘ p)
  tube u i = iso (p i) .to (f u i)

  base : B (p r) [ φ ↦ tube ◆ r ]
  base = (iso (p r) .to a₀ , λ u → cong (iso (p r) .to) (ex u))

  inB = β .lift S r p φ tube base

  rec : Comp S r _ φ f (a₀ , ex)
  rec .comp s .fst = iso (p s) .from (inB .comp s .fst)
  rec .comp s .snd u =
    symm (appCong (iso (p s) .inv₁))
    ∙ cong (iso (p s) .from) (inB .comp s .snd u)
  rec .cap =
    cong (iso (p r) .from) (inB .cap)
    ∙ appCong (iso (p r) .inv₁)

isomorphicIsFib A B iso β .vary S T σ r p φ f (a₀ , ex) s =
  cong (iso (p (⟪ σ ⟫ s)) .from)
    (β .vary S T σ r p φ
      (λ u i → iso (p i) .to (f u i))
      ((iso (p (⟪ σ ⟫ r)) .to a₀ , λ u → cong (iso (p (⟪ σ ⟫ r)) .to) (ex u)))
      s)

----------------------------------------------------------------------
-- Lemmas for proving equality of compositions
----------------------------------------------------------------------

boxEq : ∀ {ℓ} (S : Shape) {A : ⟨ S ⟩ → Set ℓ}
  {φ₀ φ₁ : CofProp} (φ : φ₀ ≡ φ₁)
  {f₀ : [ φ₀ ] → Π A} {f₁ : [ φ₁ ] → Π A}
  (f : ∀ u v → f₀ u ≡ f₁ v)
  (r : ⟨ S ⟩)
  {x₀ : A r [ φ₀ ↦ f₀ ◆ r ]} {x₁ : A r [ φ₁ ↦ f₁ ◆ r ]}
  (x : x₀ .fst ≡ x₁ .fst)
  → _≡_ {A = Σ φ ∈ CofProp , Σ f ∈ ([ φ ] → Π A) , A r [ φ ↦ f ◆ r ]}
    (φ₀ , f₀ , x₀) (φ₁ , f₁ , x₁)
boxEq S {A} {φ₀} refl f r x =
  Σext refl
    (cong
      {A = Σ p ∈ (([ φ₀ ] → Π A) × A r) , ∀ u → p .fst u r ≡ p .snd}
      (λ {((f' , a') , eq) → (f' , (a' , eq))})
      (Σext
        (×ext
          (funext λ u → f u u)
          x)
        (funext λ _ → uipImp)))

boxEqDep : ∀ {ℓ ℓ'} (S : Shape) {B : Set ℓ} {A : B → ⟨ S ⟩ → Set ℓ'}
  {b₀ b₁ : B} (b : b₀ ≡ b₁)
  {φ₀ φ₁ : CofProp} (φ : φ₀ ≡ φ₁)
  {f₀ : [ φ₀ ] → Π (A b₀)} {f₁ : [ φ₁ ] → Π (A b₁)}
  (f : ∀ u v → subst (λ b' → Π (A b')) b (f₀ u) ≡ f₁ v)
  (r : ⟨ S ⟩)
  {x₀ : A b₀ r [ φ₀ ↦ f₀ ◆ r ]} {x₁ : A b₁ r [ φ₁ ↦ f₁ ◆ r ]}
  (x : subst (A ◆ r) b (x₀ .fst) ≡ x₁ .fst)
  → subst (λ b → Σ φ ∈ CofProp , Σ f ∈ ([ φ ] → Π (A b)) , A b r [ φ ↦ f ◆ r ]) b (φ₀ , f₀ , x₀)
    ≡ (φ₁ , f₁ , x₁)
boxEqDep S refl φ f r x = boxEq S φ f r x
