{-

Definition of shapes and Path types.

-}
{-# OPTIONS --rewriting #-}
module shape where

open import prelude

----------------------------------------------------------------------
-- Shapes
----------------------------------------------------------------------

postulate
  Shape : Set
  ShapeHom : Shape → Shape → Set

  ⟨_⟩ : Shape → Set
  ⟪_⟫ : {I J : Shape} → ShapeHom I J → ⟨ I ⟩ → ⟨ J ⟩

  int : Shape

Int = ⟨ int ⟩

postulate
  O : Int
  I : Int
  O≠I   : ∀ {ℓ} {A : Set ℓ} → O ≡ I → A

----------------------------------------------------------------------
-- Path types
----------------------------------------------------------------------

record _~~_ {A : Int → Set}(a : A O)(a' : A I) : Set where
  constructor path
  field
    at : Π A
    atO : at O ≡ a
    atI : at I ≡ a'

open _~~_ public

_~_ : {A : Set}(a a' : A) → Set
_~_ {A} a a' = _~~_ {A = λ _ → A} a a'

refl~ : {A : Set}(a : A) → a ~ a
refl~ a = path (λ _ → a) refl refl

PathExt : {A : Set}{a a' : A}{p q : a ~ a'} → (∀ i → p .at i ≡ q .at i) → p ≡ q
PathExt {A = A} {a} {a'} t =
  cong
    {A = Σ (Int → A) λ p → Σ (p O ≡ a) (λ _ → p I ≡ a')}
    (λ {(l , l₀ , l₁) → path l l₀ l₁})
    (Σext (funext t) (Σext uipImp uipImp))

eqToPath : {A : Set} {x y : A} → x ≡ y → x ~ y
eqToPath {x = x} p = path (λ _ → x) refl p
