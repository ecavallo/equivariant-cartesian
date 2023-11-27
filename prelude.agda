{-

Basics.

-}
{-# OPTIONS --rewriting #-}
module prelude where

open import Agda.Primitive public renaming (Set to Type)

private variable ℓ ℓ' ℓ'' ℓ''' : Level

infix  1 Σ _⊢_
infixr 3 _,_ _,,_ _×_ _⊎_
infixr 5 _∘_ _∙_

------------------------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------------------------

Π : {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Π B = (a : _) → B a

id : {A : Type ℓ} → A → A
id x = x

_∘_ : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) x = g (f x)

_$_ : {A : Type ℓ} {B : A → Type ℓ'} → ((a : A) → B a) → (a : A) → B a
f $ a = f a

_◆_ : {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
  → ((a : A) (b : B) → C a b) → (b : B) (a : A) → C a b
(f ◆ b) a = f a b

_⊢_ : (Γ : Type ℓ) → (Γ → Type ℓ') → Type (ℓ ⊔ ℓ')
(Γ ⊢ A) = Π A

------------------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------------------

open import Agda.Builtin.Equality public

{-# BUILTIN REWRITE _≡_ #-}

_∙_ : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
refl ∙ q = q

sym : {A : Type ℓ} {x y : A} (p : x ≡ y) → y ≡ x
sym refl = refl

cong : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
cong _ refl = refl

cong₂ : {A : Type ℓ} {A' : Type ℓ'} {B : Type ℓ''}
  (f : A → A' → B) {x y : A} (p : x ≡ y) {x' y' : A'} (q : x' ≡ y')
  → f x x' ≡ f y y'
cong₂ _ refl refl = refl

subst : {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x → B y
subst _ refl b = b

coe : {A B : Type ℓ} → A ≡ B → A → B
coe = subst id

congdep : {A : Type ℓ} {B : A → Type ℓ'}
  (f : (a : A) → B a) {x y : A} (p : x ≡ y) → subst B p (f x) ≡ f y
congdep _ refl = refl

congΣ : {A : Type ℓ} {A' : A → Type ℓ'} {B : Type ℓ''}
  (f : (a : A) → A' a → B)
  {x y  : A} (p : x ≡ y)
  {x' : A' x} {y' : A' y} (q : subst A' p x' ≡ y')
  → f x x' ≡ f y y'
congΣ _ refl refl = refl

congdep₂ : {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
  (f : (a : A) → B a → C a)
  {x y : A} (p : x ≡ y)
  {z : B x} {w : B y} (q : subst B p z ≡ w)
  → subst C p (f x z) ≡ f y w
congdep₂ _ refl refl = refl

substCongAssoc : {A : Type ℓ} {B : Type ℓ'}
  (C : B → Type ℓ'') (f : A → B)
  {x y : A} (p : x ≡ y)
  (b : C (f x))
  → subst (λ x → C (f x)) p b ≡ subst C (cong f p) b
substCongAssoc _ _ refl _ = refl

substConst : {A : Type ℓ} (B : A → Type ℓ')
  {x : A} (p : x ≡ x) (b : B x)
  → subst B p b ≡ b
substConst _ refl b = refl

substTrans : {A : Type ℓ} (B : A → Type ℓ')
  {x y z : A} (q : y ≡ z) (p : x ≡ y) {b : B x}
  → subst B (p ∙ q) b ≡ subst B q (subst B p b)
substTrans B refl refl = refl

substNaturality : {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ'')
  (η : ∀ a → B a → C a)
  {a a' : A} (p : a ≡ a') (b : B a)
  → η a' (subst B p b) ≡ subst C p (η a b)
substNaturality B C η refl b = refl

appCong : {A : Type ℓ} {B : A → Type ℓ'} {f g : (a : A) → B a}
  {x : A} (p : f ≡ g) → f x ≡ g x
appCong p = cong (λ h → h _) p

adjustSubstEq : {A : Type ℓ} (B : A → Type ℓ')
  {x y z w : A} (p : x ≡ z) (p' : y ≡ z) (q : x ≡ w) (q' : y ≡ w)
  {b : B x} {b' : B y}
  → subst B p b ≡ subst B p' b'
  → subst B q b ≡ subst B q' b'
adjustSubstEq B refl refl refl refl = id

------------------------------------------------------------------------------------------
-- Uniqueness of identity proofs
------------------------------------------------------------------------------------------

uip : {A : Type ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

uipImp : {A : Type ℓ} {x y : A} {p q : x ≡ y} → p ≡ q
uipImp {p = refl} {q = refl} = refl

------------------------------------------------------------------------------------------
-- Unit type
------------------------------------------------------------------------------------------

record 𝟙 : Type where
  constructor tt

------------------------------------------------------------------------------------------
-- Σ-types
------------------------------------------------------------------------------------------

record Σ (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

syntax Σ A (λ x → B) = Σ x ∈ A , B

_×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

_×id : {A : Type ℓ} {A' : Type ℓ'} {B : A' → Type ℓ''}
  (f : A → A') → Σ A (B ∘ f) → Σ A' B
(f ×id) ab .fst = f (ab .fst)
(f ×id) ab .snd = ab .snd

id× : {A : Type ℓ} {B : A → Type ℓ'} {B' : A → Type ℓ''}
  (f : ∀ {a} → B a → B' a) → Σ A B → Σ A B'
(id× f) ab .fst = ab .fst
(id× f) ab .snd = f (ab .snd)

×ext : {A : Type ℓ} {B : Type ℓ'}
  {x x' : A} (p : x ≡ x')
  {y y' : B} (q : y ≡ y')
  → (x , y) ≡ (x' , y')
×ext refl refl = refl

Σext : {A : Type ℓ} {B : A → Type ℓ'}
  {ab ab' : Σ A B}
  (p : ab .fst ≡ ab' .fst)
  (q : subst B p (ab .snd) ≡ ab' .snd)
  → ab ≡ ab'
Σext refl refl = refl

Σeq₂ : {A  : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B}
  (p : x ≡ y) (q : x .fst ≡ y .fst)
  → subst B q (x .snd) ≡ y .snd
Σeq₂ refl refl = refl

_,,_ : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  (f : (a : A) → B a) → ((a : A) → C a (f a)) → ((a : A) → Σ (B a) (C a))
(f ,, g) a .fst = f a
(f ,, g) a .snd = g a

uncurry : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  → (∀ a b → C a b)
  → ((p : Σ A B) → C (p .fst) (p .snd))
uncurry f ab = f (ab .fst) (ab .snd)

curry : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  → ((p : Σ A B) → C (p .fst) (p .snd))
  → (∀ a b → C a b)
curry f a b = f (a , b)

------------------------------------------------------------------------------------------
-- Empty type
------------------------------------------------------------------------------------------

data 𝟘 : Type where

𝟘-elim : {A : 𝟘 → Type ℓ} → (v : 𝟘) → A v
𝟘-elim ()

𝟘-rec : {A : Type ℓ} → 𝟘 → A
𝟘-rec ()

------------------------------------------------------------------------------------------
-- Disjoint union
------------------------------------------------------------------------------------------

data _⊎_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

[_∣_] : {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''}
  → ((a : A) → C (inl a))
  → ((b : B) → C (inr b))
  → (z : A ⊎ B) → C z
[ f ∣ g ] (inl a) = f a
[ f ∣ g ] (inr b) = g b

_⊎`_ : {A : Type ℓ} {A' : Type ℓ'} {B : Type ℓ''} {B' : Type ℓ'''}
  → (A → A') → (B → B') → (A ⊎ B) → (A' ⊎ B')
(f ⊎` g) = [ inl ∘ f ∣ inr ∘ g ]

∇ : {A : Type ℓ} → A ⊎ A → A
∇ = [ id ∣ id ]

------------------------------------------------------------------------------------------
-- Retracts
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
retractExt refl refl = cong (makeRetract _ _) uipImp

------------------------------------------------------------------------------------------
-- Isomorphism
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
-- Propositions
------------------------------------------------------------------------------------------

isProp : Type ℓ → Type ℓ
isProp A = (a b : A) → a ≡ b

------------------------------------------------------------------------------------------
-- Pointed sets
------------------------------------------------------------------------------------------

Type* : ∀ ℓ → Type (lsuc ℓ)
Type* ℓ = Σ (Type ℓ) id

------------------------------------------------------------------------------------------
-- Flat modality
------------------------------------------------------------------------------------------

data ♭ {@♭ ℓ} (@♭ A : Type ℓ) : Type ℓ where
  in♭ : @♭ A → ♭ A

cong♭ : {@♭ ℓ ℓ' : Level} {@♭ A : Type ℓ} {@♭ B : Type ℓ'}
  (f : @♭ A → B) {@♭ x y : A} (@♭ p : x ≡ y) → f x ≡ f y
cong♭ _ refl = refl

appCong♭ : {@♭ ℓ ℓ' : Level} {@♭ A : Type ℓ} {@♭ B : A → Type ℓ'}
  {f g : (@♭ a : A) → B a}
  {@♭ x : A} (p : f ≡ g) → f x ≡ g x
appCong♭ p = cong (λ h → h _) p
