{-

Defines fibration structures and fibrations.

-}
{-# OPTIONS --rewriting #-}
module fibration.fibration where

open import prelude
open import axioms

private variable ℓ ℓ' ℓ'' ℓ''' : Level

----------------------------------------------------------------------
-- Open boxes
----------------------------------------------------------------------

record OpenBox (S : Shape) (r : ⟨ S ⟩) (A : ⟨ S ⟩ → Type ℓ) : Type ℓ
  where
  constructor makeBox
  field
    cof : CofProp
    tube : [ cof ] → Π A
    cap : A r [ cof ↦ tube ◆ r ]

open OpenBox public

reshapeBox : {S T : Shape} (σ : ShapeHom S T)
  {r : ⟨ S ⟩} {A : ⟨ T ⟩ → Type ℓ}
  → OpenBox T (⟪ σ ⟫ r) A → OpenBox S r (A ∘ ⟪ σ ⟫)
reshapeBox σ box .cof = box .cof
reshapeBox σ box .tube u = box .tube u ∘ ⟪ σ ⟫
reshapeBox σ box .cap = box .cap

mapBox : {S : Shape} {r : ⟨ S ⟩}
  {A : ⟨ S ⟩ → Type ℓ} {B : ⟨ S ⟩ → Type ℓ'}
  → (∀ s → A s → B s)
  → OpenBox S r A → OpenBox S r B
mapBox f box .cof = box .cof
mapBox f box .tube u i = f i (box .tube u i)
mapBox f box .cap .out = f _ (box .cap .out)
mapBox f box .cap .out≡ u = cong (f _) (box .cap .out≡ u)

opaque
  boxExt : {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ}
    {box box' : OpenBox S r A}
    → box .cof ≡ box' .cof
    → (∀ u v → box .tube u ≡ box' .tube v)
    → box .cap .out ≡ box' .cap .out
    → box ≡ box'
  boxExt {box = box} refl q refl =
    congΣ (λ t c → makeBox (box .cof) t (makeRestrict (box .cap .out) c))
      (funext λ _ → q _ _)
      (funext λ _ → uipImp)

  boxExtDep : {S : Shape} {B : Type ℓ} {A : B → ⟨ S ⟩ → Type ℓ'}
    {b₀ b₁ : B} (b : b₀ ≡ b₁)
    {r : ⟨ S ⟩}
    {box₀ : OpenBox S r (A b₀)} {box₁ : OpenBox S r (A b₁)}
    → box₀ .cof ≡ box₁ .cof
    → (∀ u v → subst (λ b' → Π (A b')) b (box₀ .tube u) ≡ box₁ .tube v)
    → subst (A ◆ r) b (box₀ .cap .out) ≡ box₁ .cap .out
    → subst (OpenBox S r ∘ A) b box₀ ≡ box₁
  boxExtDep refl f r x = boxExt f r x

----------------------------------------------------------------------
-- Solutions to individual lifting problems
----------------------------------------------------------------------

record Filler {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ} (box : OpenBox S r A) : Type ℓ
  where
  constructor makeFiller
  field
    fill : (s : ⟨ S ⟩) → A s [ box .cof ↦ box .tube ◆ s ]
    cap≡ : fill r .out ≡ box .cap .out

open Filler public

reshapeFiller : {S T : Shape} (σ : ShapeHom S T)
  {r : ⟨ S ⟩} {A : ⟨ T ⟩ → Type ℓ}
  {box : OpenBox T (⟪ σ ⟫ r) A}
  → Filler box
  → Filler (reshapeBox σ box)
reshapeFiller σ w .fill = w .fill ∘ ⟪ σ ⟫
reshapeFiller σ w .cap≡ = w .cap≡

opaque
  fillerExt : {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ}
    {box : OpenBox S r A}
    {co co' : Filler box}
    → (∀ s → co .fill s .out ≡ co' .fill s .out)
    → co ≡ co'
  fillerExt p =
    congΣ makeFiller (funext λ s → restrictExt (p s)) uipImp

  fillerCong : {S : Shape} {r : ⟨ S ⟩} {A : ⟨ S ⟩ → Type ℓ}
    {box : OpenBox S r A}
    {co co' : Filler box}
    → co ≡ co'
    → (∀ s → co .fill s .out ≡ co' .fill s .out)
  fillerCong p s = cong out (appCong (cong fill p))

----------------------------------------------------------------------
-- Equivariant fibrations
----------------------------------------------------------------------

record isFib {Γ : Type ℓ} (A : Γ → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor makeFib
  field
    lift : ∀ S r p → (box : OpenBox S r (A ∘ p)) → Filler box
    vary : ∀ S T → (σ : ShapeHom S T) → ∀ r p box s
      → reshapeFiller σ (lift T (⟪ σ ⟫ r) p box) .fill s .out
        ≡ lift S r (p ∘ ⟪ σ ⟫) (reshapeBox σ box) .fill s .out

open isFib public

Fib : (ℓ' : Level) (Γ : Type ℓ) → Type (ℓ ⊔ lsuc ℓ')
Fib ℓ' Γ = Σ (Γ → Type ℓ') isFib

----------------------------------------------------------------------
-- Fibrations can be reindexed
----------------------------------------------------------------------

reindex : {Δ : Type ℓ} {Γ : Type ℓ'} {A : Γ → Type ℓ''}
  (α : isFib A) (ρ : Δ → Γ) → isFib (A ∘ ρ)
reindex α ρ .lift S r p = α .lift S r (ρ ∘ p)
reindex α ρ .vary S T σ r p = α .vary S T σ r (ρ ∘ p)

reindexFib : {Δ : Type ℓ} {Γ : Type ℓ'} (Aα : Fib ℓ'' Γ) (ρ : Δ → Γ)
  → Fib ℓ'' Δ
reindexFib (A , α) ρ .fst = A ∘ ρ
reindexFib (A , α) ρ .snd = reindex α ρ

reindexSubst : {Δ : Type ℓ} {Γ : Type ℓ'} {A A' : Γ → Type ℓ''}
 (ρ : Δ → Γ) (P : A ≡ A') (Q : A ∘ ρ ≡ A' ∘ ρ) (α : isFib A)
  → reindex (subst isFib P α) ρ ≡ subst isFib Q (reindex α ρ)
reindexSubst ρ refl refl α = refl

----------------------------------------------------------------------
-- Reindexing is functorial
----------------------------------------------------------------------

reindexId : {Γ : Type ℓ}{A : Γ → Type ℓ'}{α : isFib A} → α ≡ reindex α id
reindexId = refl

reindexTrans :
  {Γ₁ : Type ℓ} {Γ₂ : Type ℓ'} {Γ₃ : Type ℓ''} {A : Γ₃ → Type ℓ'''}
  (α : isFib A) (f : Γ₁ → Γ₂) (g : Γ₂ → Γ₃)
  → ----------------------
  reindex α (g ∘ f) ≡ reindex (reindex α g) f
reindexTrans α g f = refl

reindexFibId : {Γ : Type ℓ} {Aα : Fib ℓ' Γ} → reindexFib Aα id ≡ Aα
reindexFibId = refl

reindexFibTrans : {Γ₁ : Type ℓ} {Γ₂ : Type ℓ'} {Γ₃ : Type ℓ''}
  {Aα : Fib ℓ''' Γ₃}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindexFib Aα (g ∘ f) ≡ reindexFib (reindexFib Aα g) f
reindexFibTrans g f = refl

----------------------------------------------------------------------
-- An extensionality principle for fibration structures
----------------------------------------------------------------------
opaque
  isFibExt :  {Γ : Type ℓ} {A : Γ → Type ℓ'} {α α' : isFib A} →
    ((S : Shape) (r : ⟨ S ⟩) (p : ⟨ S ⟩ → Γ) (box : OpenBox S r (A ∘ p))
      → (s : ⟨ S ⟩) → α .lift S r p box .fill s .out ≡ α' .lift S r p box .fill s .out)
    → α ≡ α'
  isFibExt q =
    congΣ makeFib
      (funext λ S → funext λ r → funext λ p → funext λ box → fillerExt (q S r p box))
      (funext λ S → funext λ T → funext λ σ → funext λ r → funext λ p → funext λ box → funext λ s →
        uipImp)

----------------------------------------------------------------------
-- A retract of a fibration is a fibration
----------------------------------------------------------------------

Retractᴵ : {Γ : Type ℓ} (A B : Γ → Type ℓ') → (Γ → Type ℓ')
Retractᴵ A B γ = Retract (A γ) (B γ)

opaque
  retractIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'} → Γ ⊢ Retractᴵ A B → isFib B → isFib A
  retractIsFib retract β .lift S r p box = filler
    where
    fillerB : Filler (mapBox (sec ∘ retract ∘ p) box)
    fillerB = β .lift S r p (mapBox (sec ∘ retract ∘ p) box)

    filler : Filler box
    filler .fill s .out = retract (p s) .ret (fillerB .fill s .out)
    filler .fill s .out≡ u =
      sym (appCong (retract (p s) .inv))
      ∙ cong (retract (p s) .ret) (fillerB .fill s .out≡ u)
    filler .cap≡ =
      cong (retract (p r) .ret) (fillerB .cap≡)
      ∙ appCong (retract (p r) .inv)

  retractIsFib retract β .vary S T σ r p box s =
    cong (retract _ .ret) (β .vary S T σ r p (mapBox (sec ∘ retract ∘ p) box) s)

  reindexRetract : {Δ : Type ℓ} {Γ : Type ℓ'}
    {A B : Γ → Type ℓ''}
    (retract : Γ ⊢ Retractᴵ A B)
    (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (retractIsFib retract β) ρ ≡ retractIsFib (retract ∘ ρ) (reindex β ρ)
  reindexRetract retract β ρ = isFibExt λ _ _ _ _ _ → refl

----------------------------------------------------------------------
-- Corollary: fibration structures can be transferred across isomorphisms
----------------------------------------------------------------------

_≅ᴵ_ : {Γ : Type ℓ} (A B : Γ → Type ℓ') → (Γ → Type ℓ')
_≅ᴵ_ A B γ = A γ ≅ B γ

isomorphIsFib : {Γ : Type ℓ} {A B : Γ → Type ℓ'}
  → Γ ⊢ A ≅ᴵ B → isFib B → isFib A
isomorphIsFib iso β = retractIsFib (isoToRetract ∘ iso) β

reindexIsomorph : {Δ : Type ℓ} {Γ : Type ℓ'} {A B : Γ → Type ℓ''}
  (iso : Γ ⊢ A ≅ᴵ B)
  (β : isFib B)
  (ρ : Δ → Γ)
  → reindex (isomorphIsFib iso β) ρ ≡ isomorphIsFib (iso ∘ ρ) (reindex β ρ)
reindexIsomorph _ = reindexRetract _
