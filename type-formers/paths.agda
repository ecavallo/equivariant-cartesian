{-

Fibrancy of Path types.

TODO factor through extension types

-}
{-# OPTIONS --rewriting #-}
module type-formers.paths where

open import prelude
open import axioms
open import fibration.fibration

record _~_ {ℓ} {A : Set ℓ}(a a' : A) : Set ℓ where
  constructor path
  field
    at : Int → A
    atO : at O ≡ a
    atI : at I ≡ a'

open _~_ public

eqToPath : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ~ y
eqToPath {x = x} p = path (λ _ → x) refl p

refl~ : ∀{ℓ} {A : Set ℓ} (a : A) → a ~ a
refl~ a = eqToPath refl

PathExt : ∀{ℓ} {A : Set ℓ} {a a' : A} {p q : a ~ a'}
  → (∀ i → p .at i ≡ q .at i) → p ≡ q
PathExt {A = A} {a} {a'} t =
  cong
    {A = Σ (Int → A) λ p → Σ (p O ≡ a) (λ _ → p I ≡ a')}
    (λ {(l , l₀ , l₁) → path l l₀ l₁})
    (Σext (funext t) (Σext uipImp uipImp))

Path' : ∀{ℓ ℓ'}{Γ : Set ℓ}(A : Γ → Set ℓ') → Σ x ∈ Γ , A x × A x → Set ℓ'
Path' A (x , (a , a')) = a ~ a'

module PathIsFibId {ℓ}
  (S : Shape) {A : ⟨ S ⟩ → Set ℓ} {a₀ : Π A} {a₁ : Π A}
  (α : isFib A)
  (r : ⟨ S ⟩) (box : OpenBox S r (λ s → a₀ s ~ a₁ s))
  where

  module _ (i : Int) where

    boxA : OpenBox S r A
    boxA .cof = box .cof ∨ ∂ i
    boxA .tube =
      ∨-rec (box .cof) (∂ i)
        (λ u s → box .tube u s .at i)
        (OI-rec i
          (λ {refl → a₀})
          (λ {refl → a₁}))
        (λ u → OI-elim i
          (λ {refl → funext λ s → box .tube u s .atO})
          (λ {refl → funext λ s → box .tube u s .atI}))
    boxA .cap .fst = box .cap .fst .at i
    boxA .cap .snd =
      ∨-elimEq (box .cof) (∂ i)
        (λ u → cong (λ q → q .at i) (box .cap .snd u))
        (OI-elim i
          (λ {refl → symm (box .cap .fst .atO)})
          (λ {refl → symm (box .cap .fst .atI)}))

    fillA = α .lift S r id boxA

abstract
  PathIsFib :
    ∀{ℓ ℓ'} {Γ : Set ℓ}
    {A : Γ → Set ℓ'}
    (α : isFib A)
    → -----------
    isFib (Path' A)
  PathIsFib {A = A} α .lift S r p box .fill s .fst =
    path
      (λ i → fillA i .fill s .fst)
      (symm (fillA O .fill s .snd ∣ inr ∣ inl refl ∣ ∣))
      (symm (fillA I .fill s .snd ∣ inr ∣ inr refl ∣ ∣))
    where
    open PathIsFibId S (reindex A α (fst ∘ p)) r box
  PathIsFib {A = A} α .lift S r p box .fill s .snd u =
    PathExt λ i → fillA i .fill s .snd ∣ inl u ∣
    where
    open PathIsFibId S (reindex A α (fst ∘ p)) r box
  PathIsFib {A = A} α .lift S r p box .cap≡ =
    PathExt λ i → fillA i .cap≡
    where
    open PathIsFibId S (reindex A α (fst ∘ p)) r box

  PathIsFib {A = A} α .vary S T σ r p box s =
    PathExt λ i →
    α .vary S T σ r (fst ∘ p) (T.boxA i) s
    ∙
    cong (λ b → α .lift S r (fst ∘ p ∘ ⟪ σ ⟫) b .fill s .fst)
      (boxExt
        refl
        (diagonalElim (box .cof ∨ ∂ i)
          (∨-elimEq (box .cof) (∂ i)
            (λ _ → refl)
            (OI-elim i
              (λ {refl → refl})
              (λ {refl → refl}))))
        refl)
    where
    module T = PathIsFibId T (reindex A α (fst ∘ p)) (⟪ σ ⟫ r) box
    module S = PathIsFibId S (reindex A α (fst ∘ p ∘ ⟪ σ ⟫)) r (reshapeBox σ box)

  ----------------------------------------------------------------------
  -- Forming Path types is stable under reindexing
  ----------------------------------------------------------------------
  reindexPath :
    ∀ {ℓ ℓ' ℓ''} {Δ : Set ℓ} {Γ : Set ℓ'}
    (A : Γ → Set ℓ'')
    (α : isFib A)
    (ρ : Δ → Γ)
    → ----------------------
    reindex (Path' A) (PathIsFib α) (ρ ×id) ≡ PathIsFib (reindex A α ρ)
  reindexPath A α ρ = isFibExt λ _ _ _ _ _ → refl
