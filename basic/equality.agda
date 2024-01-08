{-

  Propositional equality in the ambient type theory.

  We use Agda's --with-K flag to make identity proofs unique (see "uip" below).

-}
module basic.equality where

open import basic.prelude
open import basic.function

private variable
  ℓ ℓ' ℓ'' : Level

data _≡_ {A : Type ℓ} (a : A) : A → Type ℓ where
  instance
    refl : a ≡ a

infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

--↓ Transitivity of equality.

_∙_ : {A : Type ℓ} {a₀ a₁ a₂ : A} (p : a₀ ≡ a₁) (q : a₁ ≡ a₂) → a₀ ≡ a₂
refl ∙ q = q

infixr 5 _∙_

--↓ Symmetry of equality.

sym : {A : Type ℓ} {a₀ a₁ : A} (p : a₀ ≡ a₁) → a₁ ≡ a₀
sym refl = refl

--↓ Substitution in a family.

subst : {A : Type ℓ} (B : A → Type ℓ') {a₀ a₁ : A} (p : a₀ ≡ a₁) → B a₀ → B a₁
subst _ refl b = b

--↓ Coercion along an equality between types.

coe : {A B : Type ℓ} → A ≡ B → A → B
coe = subst id

--↓ Congruence of equality.

cong : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {a₀ a₁ : A} (p : a₀ ≡ a₁) → f a₀ ≡ f a₁
cong _ refl = refl

--↓ Congruence for two-argument functions.

cong₂ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (f : A → B → C) {a₀ a₁ : A} (p : a₀ ≡ a₁) {b₀ b₁ : B} (q : b₀ ≡ b₁)
  → f a₀ b₀ ≡ f a₁ b₁
cong₂ _ refl refl = refl

congΣ : {A : Type ℓ} {B : A → Type ℓ'} {C : Type ℓ''}
  (f : (a : A) → B a → C)
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {b₀ : B a₀} {b₁ : B a₁} (q : subst B p b₀ ≡ b₁)
  → f a₀ b₀ ≡ f a₁ b₁
congΣ _ refl refl = refl

congΣ+ : {A : Type ℓ} {B : A → Type ℓ'} {C : Type ℓ''}
  (f : (a : A) → B a → C)
  {a₀ a₁ : A} (p : a₀ ≡ a₁) ⦃ p' : B a₀ ≡ B a₁ ⦄
  {b₀ : B a₀} {b₁ : B a₁} (q : coe p' b₀ ≡ b₁)
  → f a₀ b₀ ≡ f a₁ b₁
congΣ+ _ refl ⦃ refl ⦄ refl = refl

--↓ Congruence for dependent functions.

congdep : {A : Type ℓ} {B : A → Type ℓ'}
  (f : (a : A) → B a) {a₀ a₁ : A} (p : a₀ ≡ a₁) → subst B p (f a₀) ≡ f a₁
congdep _ refl = refl

congdep₂ : {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
  (f : (a : A) → B a → C a)
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {b₀ : B a₀} {b₁ : B a₁} (q : subst B p b₀ ≡ b₁)
  → subst C p (f a₀ b₀) ≡ f a₁ b₁
congdep₂ _ refl refl = refl

--↓ Congruence for function application.

cong$ : {A : Type ℓ} {B : A → Type ℓ'} {f g : (a : A) → B a}
  {a : A} (p : f ≡ g) → f a ≡ g a
cong$ p = cong (_$ _) p

--↓ Interaction between substitution and congruence.

opaque
  substCongAssoc : {A : Type ℓ} {B : Type ℓ'}
    (C : B → Type ℓ'') (f : A → B)
    {a₀ a₁ : A} (p : a₀ ≡ a₁)
    (b : C (f a₀))
    → subst (C ∘ f) p b ≡ subst C (cong f p) b
  substCongAssoc _ _ refl _ = refl

--↓ Substitution in a constant family.

opaque
  substConst : {A : Type ℓ} {B : Type ℓ'}
    {a₀ a₁ : A} (p : a₀ ≡ a₁) (b : B)
    → subst (cst B) p b ≡ b
  substConst refl b = refl

--↓ Naturality of substitution.

opaque
  substNaturality : {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
    (η : ∀ {a} → B a → C a)
    {a₀ a₁ : A} (p : a₀ ≡ a₁) {b : B a₀}
    → η (subst B p b) ≡ subst C p (η b)
  substNaturality η refl = refl

--↓ Substitution in a family of function types where only the domain varies.

opaque
  substDom : {A : Type ℓ} (B : A → Type ℓ') {C : Type ℓ''}
    {a₀ a₁ : A} (p : a₀ ≡ a₁) (f : B a₀ → C)
    → subst (λ a → B a → C) p f ≡ f ∘ subst B (sym p)
  substDom _ refl f = refl

--↓ Utility function for moving substitutions around.

opaque
  adjustSubstEq : {A : Type ℓ} (B : A → Type ℓ')
    {a₀ a₁ a₂ a₃ : A}
    (p₀₂ : a₀ ≡ a₂) (p₁₂ : a₁ ≡ a₂) (p₀₃ : a₀ ≡ a₃) (p₁₃ : a₁ ≡ a₃)
    {b₀ : B a₀} {b₁ : B a₁}
    → subst B p₀₂ b₀ ≡ subst B p₁₂ b₁
    → subst B p₀₃ b₀ ≡ subst B p₁₃ b₁
  adjustSubstEq B refl refl refl refl = id

------------------------------------------------------------------------------------------
-- Uniqueness of identity proofs.
------------------------------------------------------------------------------------------

--↓ The --with-K flag allows us to prove this with pattern-matching.

uip : {A : Type ℓ} {a₀ a₁ : A} (p q : a₀ ≡ a₁) → p ≡ q
uip refl refl = refl

--↓ Variant with implicit arguments.

uip' : {A : Type ℓ} {a₀ a₁ : A} {p q : a₀ ≡ a₁} → p ≡ q
uip' = uip _ _

------------------------------------------------------------------------------------------
-- Propositions with respect to strict equality.
------------------------------------------------------------------------------------------

isStrictProp : (A : Type ℓ) → Type ℓ
isStrictProp A = (a₀ a₁ : A) → a₀ ≡ a₁
