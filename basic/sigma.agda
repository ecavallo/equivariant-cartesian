{-

  Σ-types.

-}
module basic.sigma where

open import basic.prelude
open import basic.function
open import basic.equality

private variable
  ℓ ℓ' ℓ'' : Level

record Σ (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infix 1 Σ
infixl 3 _,_

syntax Σ A (λ a → B) = Σ a ∈ A , B

--↓ Non-dependent products.

_×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Σ A (cst B)

infixr 3 _×_

_×id : {A : Type ℓ} {A' : Type ℓ'} {B : A' → Type ℓ''}
  (f : A → A') → Σ A (B ∘ f) → Σ A' B
(f ×id) ab .fst = f (ab .fst)
(f ×id) ab .snd = ab .snd

--↓ Extensionality for Σ-types.

opaque
  Σext : {A : Type ℓ} {B : A → Type ℓ'} {t₀ t₁ : Σ A B}
    (eq : t₀ .fst ≡ t₁ .fst)
    → subst B eq (t₀ .snd) ≡ t₁ .snd
    → t₀ ≡ t₁
  Σext refl refl = refl

opaque
  ×ext : {A : Type ℓ} {B : Type ℓ'} {t₀ t₁ : A × B}
    → t₀ .fst ≡ t₁ .fst
    → t₀ .snd ≡ t₁ .snd
    → t₀ ≡ t₁
  ×ext refl refl = refl

opaque
  Σeq₂ : {A  : Type ℓ} {B : A → Type ℓ'} {t₀ t₁ : Σ A B}
    (p : t₀ ≡ t₁) (q : t₀ .fst ≡ t₁ .fst)
    → subst B q (t₀ .snd) ≡ t₁ .snd
  Σeq₂ refl refl = refl

--↓ Currying and uncurrying.

uncurry : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  → (∀ a b → C a b)
  → (∀ t → C (t .fst) (t .snd))
uncurry f t = f (t .fst) (t .snd)

curry : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  → (∀ t → C (t .fst) (t .snd))
  → (∀ a b → C a b)
curry f a b = f (a , b)
