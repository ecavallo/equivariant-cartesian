{-

Definition of composition and fibrations.

-}
{-# OPTIONS --rewriting #-}
module fibrations where

open import prelude
open import interval
open import cofprop

----------------------------------------------------------------------
-- Composition structure
----------------------------------------------------------------------

record Comp (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ → Set) (φ : CofProp)
  (f : [ φ ] → Π A) (x₀ : A r [ φ ↦ f ◆ r ]) : Set
  where
  field
    comp : (s : ⟨ S ⟩) → A s [ φ ↦ f ◆ s ]
    cap : comp r .fst ≡ x₀ .fst

open Comp public

reshapeComp : {S T : Shape} (σ : ShapeHom S T)
  → ∀ {r A φ f x₀}
  → Comp T (⟪ σ ⟫ r) A φ f x₀
  → Comp S r (A ∘ ⟪ σ ⟫) φ (f ◇ ⟪ σ ⟫) x₀
reshapeComp σ w =
  record
  { comp = w .comp ∘ ⟪ σ ⟫
  ; cap = w .cap
  }

compExt : {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Set} {φ : CofProp}
  {f : [ φ ] → Π A} {x₀ : A r [ φ ↦ f ◆ r ]}
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
record isFib {ℓ} {Γ : Set ℓ} (A : Γ → Set) : Set ℓ where
  field
    lift : ∀ S r p φ f x₀ → Comp S r (A ∘ p) φ f x₀
    vary : ∀ S T → (σ : ShapeHom S T) → ∀ r p φ f x₀ s
      → lift T (⟪ σ ⟫ r) p φ f x₀ .comp (⟪ σ ⟫ s) .fst
        ≡ lift S r (p ∘ ⟪ σ ⟫) φ (f ◇ ⟪ σ ⟫) x₀ .comp s .fst

open isFib public

Fib : ∀{a}(Γ : Set a) → Set (lsuc lzero ⊔ a)
Fib {a} Γ = Σ (Γ → Set) isFib

----------------------------------------------------------------------
-- Fibrations can be reindexed
----------------------------------------------------------------------
reindex : ∀{a a'}{Δ : Set a}{Γ : Set a'}(A : Γ → Set)(α : isFib A)(ρ : Δ → Γ) → isFib (A ∘ ρ)
reindex A α ρ =
  record
  { lift = λ S r p → α .lift S r (ρ ∘ p)
  ; vary = λ S T σ r p → α .vary S T σ r (ρ ∘ p)
  }

reindex' : ∀{a a'}{Δ : Set a}{Γ : Set a'}(Aα : Fib Γ)(ρ : Δ → Γ) → Fib Δ
reindex' (A , α) ρ = (A ∘ ρ , reindex A α ρ)

reindexSubst : ∀ {ℓ ℓ'} {Δ : Set ℓ} {Γ : Set ℓ'} {A A' : Γ → Set}
 (ρ : Δ → Γ)(P : A ≡ A') (Q : A ∘ ρ ≡ A' ∘ ρ) (α : isFib A)
  → reindex A' (subst isFib P α) ρ ≡ subst isFib Q (reindex A α ρ)
reindexSubst ρ refl refl α = refl

----------------------------------------------------------------------
-- Reindexing is functorial
----------------------------------------------------------------------
reindexAlongId : ∀{a}{Γ : Set a}{A : Γ → Set}{α : isFib A} → α ≡ reindex A α id
reindexAlongId = refl

reindexComp :
  ∀{a b c}{Γ₁ : Set a}{Γ₂ : Set b}{Γ₃ : Set c}{A : Γ₃ → Set}{α : isFib A}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex A α (g ∘ f) ≡ reindex (A ∘ g) (reindex A α g) f
reindexComp g f = refl

reindexAlongId' : ∀{a}{Γ : Set a}{A : Fib Γ} → reindex' A id ≡ A
reindexAlongId' = refl

reindexComp' :
  ∀{a b c}{Γ₁ : Set a}{Γ₂ : Set b}{Γ₃ : Set c}
  {A : Fib Γ₃}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex' A (g ∘ f) ≡ reindex' (reindex' A g) f
reindexComp' g f = refl

----------------------------------------------------------------------
-- An extensionality principle for fibration structures
----------------------------------------------------------------------
fibExt : ∀{ℓ}{Γ : Set ℓ}{A : Γ → Set}{α α' : isFib A} →
  ((S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → Γ) (φ : CofProp)
  (f : [ φ ] → Π (A ∘ p)) (x₀ : A (p r) [ φ ↦ f ◆ r ])
    → (s : ⟨ S ⟩) → α .lift S r p φ f x₀ .comp s .fst ≡ α' .lift S r p φ f x₀ .comp s .fst)
  → α ≡ α'
fibExt {Γ = Γ} {A} {α} {α'} q =
  cong
    (λ {(l , u) → record {lift = l; vary = u}})
    (Σext
      (funext λ S → funext λ r → funext λ p → funext λ φ → funext λ f → funext λ x₀ →
        compExt (q S r p φ f x₀))
      (funext λ S → funext λ T → funext λ σ → funext λ r → funext λ p →
        funext λ φ → funext λ f → funext λ x₀ → funext λ s →
          uipImp))

----------------------------------------------------------------------
-- Terminal object is fibrant
----------------------------------------------------------------------
FibUnit : {Γ : Set} → isFib(λ(_ : Γ) → Unit)
FibUnit .lift _ _ _ _ _ (unit , _) .comp _ = (unit , λ _ → refl)
FibUnit .lift _ _ _ _ _ (unit , _) .cap = refl
FibUnit .vary _ _ _ _ _ _ _ (unit , _) _ = refl

----------------------------------------------------------------------
-- Initial object is fibrant
----------------------------------------------------------------------
Fib∅ : {Γ : Set} → isFib(λ(_ : Γ) → ∅)
Fib∅ .lift _ _ _ _ _ (() , _)
Fib∅ .vary _ _ _ _ _ _ _ (() , _)

----------------------------------------------------------------------
-- Fibrations are closed under isomorphism
----------------------------------------------------------------------
_≅'_ : ∀{a}{Γ : Set a}(A B : Γ → Set) → Set a
_≅'_ {_} {Γ} A B = (x : Γ) → A x ≅ B x

FibIso : ∀{a}{Γ : Set a}(A B : Γ → Set) → (A ≅' B) → isFib B → isFib A
FibIso A B iso β .lift S r p φ f (a₀ , ex) =
  record
  { comp = λ s →
    ( iso (p s) .from (inB .comp s .fst)
    , λ u →
      trans
        (cong (iso (p s) .from) (inB .comp s .snd u))
        (symm (appCong (iso (p s) .inv₁)))
    )
  ; cap =
    trans
      (appCong (iso (p r) .inv₁))
      (cong (iso (p r) .from) (inB .cap))
  }
  where
  tube : [ φ ] → Π (B ∘ p)
  tube u i = iso (p i) .to (f u i)

  base : B (p r) [ φ ↦ tube ◆ r ]
  base = (iso (p r) .to a₀ , λ u → cong (iso (p r) .to) (ex u))

  inB = β .lift S r p φ tube base
FibIso A B iso β .vary S T σ r p φ f (a₀ , ex) s =
  cong (iso (p (⟪ σ ⟫ s)) .from)
    (β .vary S T σ r p φ
      (λ u i → iso (p i) .to (f u i))
      ((iso (p (⟪ σ ⟫ r)) .to a₀ , λ u → cong (iso (p (⟪ σ ⟫ r)) .to) (ex u)))
      s)

----------------------------------------------------------------------
-- Lemmas for proving equality of compositions
----------------------------------------------------------------------

boxEq : (S : Shape) {A : ⟨ S ⟩ → Set}
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
      {A = Σ p ∈ (([ φ₀ ] → Π A) × A r) , (p .fst ◆ r ↗ p .snd)}
      (λ {((f' , a') , eq) → (f' , (a' , eq))})
      (Σext
        (×ext
          (funext λ u → f u u)
          x)
        (funext λ _ → uipImp)))

boxEqDep : (S : Shape) {B : Set} {A : B → ⟨ S ⟩ → Set} 
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
