{-

Basics.

-}
module prelude where

open import Agda.Primitive public renaming (Set to Type)

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level

infix  1 Σ
infixl 3 _,_
infixr 3 _×_ _⊎_
infix 4 _≡_ _≅_


infixr 5 _∘_ _∙_ _$_ _$♭_

-----------------------------------------------------------------------------------------
-- Functions.
------------------------------------------------------------------------------------------

--↓ Alternate notation for Π-types.

Π : (A : Type ℓ) → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Π A B = (a : _) → B a

--↓ Identity function.

id : {A : Type ℓ} → A → A
id a = a

--↓ Constant function.

cst : {A : Type ℓ} {B : Type ℓ''} → B → A → B
cst b a = b

--↓ Composition of (dependent) functions.

_∘_ : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)

--↓ Function application.

_$_ : {A : Type ℓ} {B : A → Type ℓ'} → ((a : A) → B a) → (a : A) → B a
f $ a = f a

--↓ Infix notation for "flip".

_⦅–⦆_ : {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
  → ((a : A) (b : B) → C a b) → (b : B) (a : A) → C a b
(f ⦅–⦆ b) a = f a b

------------------------------------------------------------------------------------------
-- Propositional equality.
--
-- We use Agda's --with-K flag to make identity proofs unique (see "uip" below).
------------------------------------------------------------------------------------------

data _≡_ {A : Type ℓ} (a : A) : A → Type ℓ where
  instance
    refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

--↓ Transitivity of equality.

_∙_ : {A : Type ℓ} {a₀ a₁ a₂ : A} (p : a₀ ≡ a₁) (q : a₁ ≡ a₂) → a₀ ≡ a₂
refl ∙ q = q

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
    (η : ∀ a → B a → C a)
    {a₀ a₁ : A} (p : a₀ ≡ a₁) {b : B a₀}
    → η a₁ (subst B p b) ≡ subst C p (η a₀ b)
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

--↓ Uniqueness of identity proofs.
--↓ The --with-K flag allows us to prove this with pattern-matching.

uip : {A : Type ℓ} {a₀ a₁ : A} (p q : a₀ ≡ a₁) → p ≡ q
uip refl refl = refl

--↓ Variant with implicit arguments.

uip' : {A : Type ℓ} {a₀ a₁ : A} {p q : a₀ ≡ a₁} → p ≡ q
uip' = uip _ _

------------------------------------------------------------------------------------------
-- Unit type.
------------------------------------------------------------------------------------------

record 𝟙 : Type where
  instance constructor tt

------------------------------------------------------------------------------------------
-- Σ-types.
------------------------------------------------------------------------------------------

record Σ (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

syntax Σ A (λ a → B) = Σ a ∈ A , B

--↓ Non-dependent products.

_×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Σ A (cst B)

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

------------------------------------------------------------------------------------------
-- Empty type and negation.
------------------------------------------------------------------------------------------

data 𝟘 : Type where

𝟘-elim : {A : 𝟘 → Type ℓ} → (v : 𝟘) → A v
𝟘-elim ()

𝟘-rec : {A : Type ℓ} → 𝟘 → A
𝟘-rec ()

¬_ : Type ℓ → Type ℓ
¬ A = A → 𝟘

------------------------------------------------------------------------------------------
-- Coproducts.
------------------------------------------------------------------------------------------

data _⊎_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

--↓ Elimination from a coproduct.

⊎-elim : {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''}
  → ((a : A) → C (inl a))
  → ((b : B) → C (inr b))
  → (z : A ⊎ B) → C z
⊎-elim f g (inl a) = f a
⊎-elim f g (inr b) = g b

[_∣_] = ⊎-elim

--↓ Functoriality of coproducts.

_⊎`_ : {A : Type ℓ} {A' : Type ℓ'} {B : Type ℓ''} {B' : Type ℓ'''}
  → (A → A') → (B → B') → (A ⊎ B) → (A' ⊎ B')
(f ⊎` g) = [ inl ∘ f ∣ inr ∘ g ]

--↓ Codiagonal function.

∇ : {A : Type ℓ} → A ⊎ A → A
∇ = [ id ∣ id ]

------------------------------------------------------------------------------------------
-- Natural numbers.
-- We import Agda's builtin natural number datatype.
------------------------------------------------------------------------------------------

open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.FromNat public using (Number ; fromNat)

instance
  Numℕ : Number ℕ
  Numℕ .Number.Constraint _ = 𝟙
  Numℕ .Number.fromNat n = n

------------------------------------------------------------------------------------------
-- Retracts.
------------------------------------------------------------------------------------------

record Retract (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
 constructor makeRetract
 field
  sec : A → B
  ret : B → A
  inv : ret ∘ sec ≡ id

open Retract public

retractExt : {A : Type ℓ} {B : Type ℓ'}
  {retract₀ retract₁ : Retract A B}
  → retract₀ .sec ≡ retract₁ .sec
  → retract₀ .ret ≡ retract₁ .ret
  → retract₀ ≡ retract₁
retractExt refl refl = cong (makeRetract _ _) uip'

------------------------------------------------------------------------------------------
-- Isomorphisms.
------------------------------------------------------------------------------------------
record _≅_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
 field
  to   : A → B
  from : B → A
  inv₁ : from ∘ to ≡ id
  inv₂ : to ∘ from ≡ id

open _≅_ public

isoToRetract : {A : Type ℓ} {B : Type ℓ'}
  → A ≅ B → Retract A B
isoToRetract iso .sec = iso .to
isoToRetract iso .ret = iso .from
isoToRetract iso .inv = iso .inv₁

------------------------------------------------------------------------------------------
-- Flat modality.
------------------------------------------------------------------------------------------

--↓ Application of a flat-modal function.

_$♭_ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} {B : A → Type ℓ'} → ((@♭ a : A) → B a) → (@♭ a : A) → B a
f $♭ a = f a

--↓ Congruence for flat-modal functions.

cong♭ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} {B : Type ℓ'}
  (f : @♭ A → B) {@♭ a₀ a₁ : A} (@♭ p : a₀ ≡ a₁) → f a₀ ≡ f a₁
cong♭ _ refl = refl

--↓ Congruence of function application for flat-model functions.

cong$♭ : ∀ {@♭ ℓ} {@♭ A : Type ℓ} {B : A → Type ℓ'}
  {f g : (@♭ a : A) → B a}
  {@♭ a : A} (p : f ≡ g) → f a ≡ g a
cong$♭ p = cong (_$♭ _) p
