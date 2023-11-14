{-

Basics.

-}
{-# OPTIONS --rewriting #-}
module prelude where

open import Agda.Primitive public

infix  1 Σ
infixr 3 _,_ _×_ _⊎_
infixr 5 _∘_ _∙_

----------------------------------------------------------------------
-- Identity function
----------------------------------------------------------------------
id : ∀{a}{A : Set a} → A → A
id x = x

----------------------------------------------------------------------
-- Composition
----------------------------------------------------------------------
_∘_ :
  {ℓ m n : Level}
  {A : Set ℓ}
  {B : A → Set m}
  {C : (a : A) → B a → Set n}
  (g : {a : A} (b : B a) → C a b)
  (f : (a : A) → B a)
  → -------------
  (a : A) → C a (f a)
(g ∘ f) x = g (f x)


----------------------------------------------------------------------
-- Propositional equality
----------------------------------------------------------------------
open import Agda.Builtin.Equality public

{-# BUILTIN REWRITE _≡_ #-}

_∙_ : -- transitivity
  {ℓ : Level}
  {A : Set ℓ}
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  → ---------
  x ≡ z
refl ∙ q = q

symm :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  (p : x ≡ y)
  → ---------
  y ≡ x
symm refl = refl

cong :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {B : Set ℓ'}
  (f : A → B)
  {x y : A}
  (p : x ≡ y)
  → -----------
  f x ≡ f y
cong _ refl = refl

cong₂ :
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ} {A' : Set ℓ'}
  {B : Set ℓ''}
  (f : A → A' → B)
  {x y  : A}
  {x' y' : A'}
  (p : x ≡ y)
  (q : x' ≡ y')
  → --------------
  f x x' ≡ f y y'
cong₂ _ refl refl = refl

subst :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  (B : A → Set ℓ')
  {x y : A}
  (p : x ≡ y)
  → --------------
  B x → B y
subst _  refl = λ b → b

congdep :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  (f : (a : A) → B a)
  {x y : A}
  (p : x ≡ y)
  → -----------
  subst B p (f x) ≡ f y
congdep _ refl = refl

congΣ :
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ} {A' : A → Set ℓ'}
  {B : Set ℓ''}
  (f : (a : A) → A' a → B)
  {x y  : A}
  {x' : A' x} {y' : A' y}
  (p : x ≡ y)
  (q : subst A' p x' ≡ y')
  → --------------
  f x x' ≡ f y y'
congΣ _ refl refl = refl

congdep₂ :
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  {C : A → Set ℓ''}
  (f : (a : A) → B a → C a)
  {x y : A}
  (p : x ≡ y)
  {z : B x} {w : B y}
  (q : subst B p z ≡ w)
  → subst C p (f x z) ≡ f y w
congdep₂ _ refl refl = refl

substCongAssoc :
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ}
  {B : Set ℓ'}
  (C : B → Set ℓ'')
  (f : A → B)
  {x y : A}
  (p : x ≡ y)
  (b : C (f x))
  → ------------------------------------------
  subst (λ x → C (f x)) p b ≡ subst C (cong f p) b
substCongAssoc _ _ refl _ = refl

substConst :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {B : Set ℓ'}
  {x y : A} (p : x ≡ y) (b : B)
  → subst (λ _ → B) p b ≡ b
substConst refl b = refl

substTrans :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y z : A}
  (q : y ≡ z) (p : x ≡ y)
  {b : B x}
  → ------------------------------------------
  subst B (p ∙ q) b ≡ subst B q (subst B p b)
substTrans B refl refl = refl

substNaturality : ∀ {ℓ ℓ' ℓ''}
  {A : Set ℓ} (B : A → Set ℓ') (C : A → Set ℓ'')
  (η : ∀ a → B a → C a)
  {a a' : A} (p : a ≡ a') (b : B a)
  → η a' (subst B p b) ≡ subst C p (η a b)
substNaturality B C η refl b = refl

uip :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  (p q : x ≡ y)
  → -----------
  p ≡ q
uip refl refl = refl

uipImp :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  {p q : x ≡ y}
  → -----------
  p ≡ q
uipImp {p = refl} {q = refl} = refl

appCong :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  {f g : (a : A) → B a}
  {x : A}
  (p : f ≡ g)
  → -----------
  f x ≡ g x
appCong p = cong (λ h → h _) p

adjustSubstEq :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y z w : A}
  (p : x ≡ z) (p' : y ≡ z)
  (q : x ≡ w) (q' : y ≡ w)
  {b : B x} {b' : B y}
  → subst B p b ≡ subst B p' b'
  → subst B q b ≡ subst B q' b'
adjustSubstEq B refl refl refl refl = id

----------------------------------------------------------------------
-- Type coercion
----------------------------------------------------------------------
coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe = subst id

----------------------------------------------------------------------
-- Empty type
----------------------------------------------------------------------
data ∅ : Set where

∅-elim :
  {ℓ : Level}
  {A : ∅ → Set ℓ}
  → ---------
  (v : ∅) → A v
∅-elim ()

∅-rec :
  {ℓ : Level}
  {A : Set ℓ}
  → ---------
  ∅ → A
∅-rec ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ∅

----------------------------------------------------------------------
-- One-element type
----------------------------------------------------------------------
open import Agda.Builtin.Unit renaming (⊤ to Unit) public

----------------------------------------------------------------------
-- Disjoint union
----------------------------------------------------------------------
data _⊎_ {ℓ m : Level}(A : Set ℓ)(B : Set m) : Set (ℓ ⊔ m) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

[_∣_] : ∀ {ℓ ℓ' ℓ''}
  {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
  → (A → C) → (B → C) → A ⊎ B → C
[ f ∣ g ] (inl a) = f a
[ f ∣ g ] (inr b) = g b

_⊎`_ : ∀ {ℓ ℓ' ℓ'' ℓ'''}
  {A : Set ℓ} {A' : Set ℓ'} {B : Set ℓ''} {B' : Set ℓ'''}
  → (A → A') → (B → B') → (A ⊎ B) → (A' ⊎ B')
(f ⊎` g) = [ inl ∘ f ∣ inr ∘ g ]

∇ : ∀ {ℓ} {A : Set ℓ} → A ⊎ A → A
∇ = [ id ∣ id ]

----------------------------------------------------------------------
-- Σ-types
----------------------------------------------------------------------
record Σ {ℓ m : Level} (A : Set ℓ) (B : A → Set m) : Set (ℓ ⊔ m) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

syntax Σ A (λ x → B) = Σ x ∈ A , B

_×_ : {ℓ m : Level} → Set ℓ → Set m → Set (ℓ ⊔ m)
A × B = Σ A (λ _ → B)

_×id : {ℓ ℓ' m : Level}{A : Set ℓ}{A' : Set ℓ'}{B : A' → Set m}
  (f : A → A') → Σ A (B ∘ f) → Σ A' B
(f ×id) (a , b) = (f a , b)

id× : {ℓ m m' : Level} {A : Set ℓ} {B : A → Set m} {B' : A → Set m'}
  (f : ∀ {a} → B a → B' a) → Σ A B → Σ A B'
(id× f) (a , b) = (a , f b)

×ext :
  {ℓ m : Level}
  {A : Set ℓ}
  {B : Set m}
  {x x' : A}
  {y y' : B}
  (p : x ≡ x')
  (q : y ≡ y')
  → --------------------
  (x , y) ≡ (x' , y')
×ext refl refl = refl

Σext :
  {ℓ m : Level}
  {A : Set ℓ}
  {B : A → Set m}
  {x x' : A}
  {y : B x}
  {y' : B x'}
  (p : x ≡ x')
  (q : subst B p y ≡ y')
  → --------------------
  (x , y) ≡ (x' , y')
Σext refl refl = refl

Σeq₂ :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  {B : A → Set ℓ'}
  {x y : Σ A B}
  (p : x ≡ y) (q : x .fst ≡ y .fst)
  → subst B q (x .snd) ≡ y .snd
Σeq₂ refl refl = refl

uncurry : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : (a : A) → B a → Set ℓ''}
  → (∀ a b → C a b)
  → ((p : Σ A B) → C (p .fst) (p .snd))
uncurry f (a , b) = f a b

curry : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : (a : A) → B a → Set ℓ''}
  → ((p : Σ A B) → C (p .fst) (p .snd))
  → (∀ a b → C a b)
curry f a b = f (a , b)

----------------------------------------------------------------------
-- Functions
----------------------------------------------------------------------
Π : ∀ {ℓ ℓ'} {A : Set ℓ} → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
Π B = (a : _) → B a

_◆_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : B → Set ℓ''}
       → (A → (i : B) → C i) → (i : B) → A → C i
(f ◆ b) a = f a b

----------------------------------------------------------------------
-- Retracts
----------------------------------------------------------------------
record Retract {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
 constructor makeRetract
 field
  sec : A → B
  ret : B → A
  inv : ret ∘ sec ≡ id

open Retract public

retractExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
  {retract₀ retract₁ : Retract A B}
  → retract₀ .sec ≡ retract₁ .sec
  → retract₀ .ret ≡ retract₁ .ret
  → retract₀ ≡ retract₁
retractExt refl refl = cong (makeRetract _ _) uipImp

----------------------------------------------------------------------
-- Isomorphism
----------------------------------------------------------------------
record _≅_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
 field
  to   : A → B
  from : B → A
  inv₁ : from ∘ to ≡ id
  inv₂ : to ∘ from ≡ id

open _≅_ public

isoToRetract : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
  → A ≅ B → Retract A B
isoToRetract iso .sec = iso .to
isoToRetract iso .ret = iso .from
isoToRetract iso .inv = iso .inv₁

----------------------------------------------------------------------
-- Propositions
----------------------------------------------------------------------

isProp : ∀ {ℓ} → Set ℓ → Set ℓ
isProp A = (a b : A) → a ≡ b

----------------------------------------------------------------------
-- Pointed sets
----------------------------------------------------------------------

Set* : ∀ ℓ → Set (lsuc ℓ)
Set* ℓ = Σ (Set ℓ) id

----------------------------------------------------------------------
-- Flat modality
----------------------------------------------------------------------

data ♭ {@♭ ℓ} (@♭ A : Set ℓ) : Set ℓ where
  in♭ : @♭ A → ♭ A

cong♭ :
  {@♭ ℓ ℓ' : Level}
  {@♭ A : Set ℓ}
  {@♭ B : Set ℓ'}
  (f : @♭ A → B)
  {@♭ x y : A}
  (@♭ p : x ≡ y)
  → -----------
  f x ≡ f y
cong♭ _ refl = refl

appCong♭ :
  {@♭ ℓ ℓ' : Level}
  {@♭ A : Set ℓ}
  {@♭ B : A → Set ℓ'}
  {f g : (@♭ a : A) → B a}
  {@♭ x : A}
  (p : f ≡ g)
  → -----------
  f x ≡ g x
appCong♭ p = cong (λ h → h _) p
