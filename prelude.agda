{-

Basics.

-}
{-# OPTIONS --rewriting #-}
module prelude where

open import Agda.Primitive public

infix  1 Σ
infixr 3 _,_ _×_ _⊎_
infixr 5 _∘_

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
  {B : Set m}
  {C : B → Set n}
  (g : (b : B) → C b)
  (f : A → B)
  → -------------
  (a : A) → C (f a)
(g ∘ f) x = g (f x)

----------------------------------------------------------------------
-- Propositional equality
----------------------------------------------------------------------
open import Agda.Builtin.Equality public

{-# BUILTIN REWRITE _≡_ #-}

trans :
  {ℓ : Level}
  {A : Set ℓ}
  {x y z : A}
  (q : y ≡ z)
  (p : x ≡ y)
  → ---------
  x ≡ z
trans q refl = q

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
  {ℓ ℓ' : Level}
  {A A' : Set ℓ}
  {B : Set ℓ'}
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

substTrans :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y z : A}
  (q : y ≡ z) (p : x ≡ y)
  {b : B x}
  → ------------------------------------------
  subst B (trans q p) b ≡ subst B q (subst B p b)
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
-- Booleans
----------------------------------------------------------------------
open import Agda.Builtin.Bool renaming (Bool to 𝔹) public

----------------------------------------------------------------------
-- Natural Numbers
----------------------------------------------------------------------
open import Agda.Builtin.Nat renaming (Nat to ℕ) public

----------------------------------------------------------------------
-- Disjoint union
----------------------------------------------------------------------
data _⊎_ {ℓ m : Level}(A : Set ℓ)(B : Set m) : Set (ℓ ⊔ m) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

----------------------------------------------------------------------
-- Propositional truncation
----------------------------------------------------------------------

postulate
  ∥_∥ : ∀ {ℓ} → Set ℓ → Set ℓ

module _ {ℓ : Level} {A : Set ℓ} where
  postulate
    ∣_∣ : A → ∥ A ∥

    trunc : (t u : ∥ A ∥) → t ≡ u

    ∥∥-rec : ∀ {ℓ'}
      (P : Set ℓ')
      (f : A → P)
      (p : ∀ a b → f a ≡ f b)
      → ---------------
      ∥ A ∥ → P

    ∥∥-rec-β : ∀ {ℓ'} (P : Set ℓ') f p → (a : A)
      → ∥∥-rec P f p ∣ a ∣ ≡ f a

    ∥∥-elim : ∀ {ℓ'}
      (P : ∥ A ∥ → Set ℓ')
      (f : (a : A) → P ∣ a ∣)
      (p : ∀ a b → subst P (trunc ∣ a ∣ ∣ b ∣) (f a) ≡ f b)
      → ---------------
      (t : ∥ A ∥) → P t

    ∥∥-elim-β : ∀ {ℓ'} (P : ∥ A ∥ → Set ℓ') f p → (a : A)
      → ∥∥-elim P f p ∣ a ∣ ≡ f a

    {-# REWRITE ∥∥-rec-β ∥∥-elim-β #-}

----------------------------------------------------------------------
-- Truncated disjunction
----------------------------------------------------------------------

∥⊎∥-rec : ∀ {ℓ ℓ' ℓ''}
  {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
  (pA : (a a' : A) → a ≡ a')
  (pB : (b b' : B) → b ≡ b')
  (f : A → C)
  (g : B → C)
  (p : ∀ a b → f a ≡ g b)
  → ∥ A ⊎ B ∥ → C
∥⊎∥-rec pA pB f g p =
  ∥∥-rec _
    (λ {(inl a) → f a ; (inr b) → g b})
    (λ
      { (inl a) (inl a') → cong f (pA a a')
      ; (inl a) (inr b') → p a b'
      ; (inr b) (inl a') → symm (p a' b)
      ; (inr b) (inr b') → cong g (pB b b')
      })

∥⊎∥-elim : ∀ {ℓ ℓ' ℓ''}
  {A : Set ℓ} {B : Set ℓ'}
  (pA : (a a' : A) → a ≡ a')
  (pB : (b b' : B) → b ≡ b')
  (C : ∥ A ⊎ B ∥ → Set ℓ'')
  (f : (a : A) → C ∣ inl a ∣)
  (g : (b : B) → C ∣ inr b ∣)
  (p : ∀ a b → subst C (trunc _ _) (f a) ≡ g b)
  → (t : ∥ A ⊎ B ∥) → C t
∥⊎∥-elim pA pB C f g p =
  ∥∥-elim _
    (λ {(inl a) → f a ; (inr b) → g b})
    (λ
      { (inl a) (inl a') →
        trans
          (trans
            (congdep f (pA a a'))
            (symm (substCongAssoc C (∣_∣ ∘ inl) (pA a a') _)))
          (cong (λ q → subst C q (f a)) (uip (trunc _ _) (cong (∣_∣ ∘ inl) (pA a a'))))
      ; (inl a) (inr b') → p a b'
      ; (inr b) (inl a') →
        adjustSubstEq C
          refl (trunc ∣ inl a' ∣ ∣ inr b ∣)
          (trunc ∣ inr b ∣ ∣ inl a' ∣) refl
          (symm (p a' b))
      ; (inr b) (inr b') →
        trans
          (trans
            (congdep g (pB b b'))
            (symm (substCongAssoc C (∣_∣ ∘ inr) (pB b b') _)))
          (cong (λ q → subst C q (g b)) (uip (trunc _ _) (cong (∣_∣ ∘ inr) (pB b b'))))
      })

----------------------------------------------------------------------
-- Dependent products
----------------------------------------------------------------------
record Σ {ℓ m : Level} (A : Set ℓ) (B : A → Set m) : Set (ℓ ⊔ m) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

_&_ : ∀ {ℓ m : Level} {A : Set ℓ} {B : A → Set m} (a : A) → B a → Σ A B
_&_ = _,_

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

Σeq₁ :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  {B : A → Set ℓ'}
  {x y : Σ A B}
  (p : x ≡ y)
  → --------------
  fst x ≡ fst y
Σeq₁ refl = refl

Σeq₂ :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  {B : A → Set ℓ'}
  {x y : Σ A B}
  (p : x ≡ y)
  → --------------
  subst B (Σeq₁ p) (x .snd) ≡ y .snd
Σeq₂ refl = refl

Σeq₂' :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  {B : A → Set ℓ'}
  {x y : Σ A B}
  (p : x ≡ y) (q : x .fst ≡ y .fst)
  → subst B q (x .snd) ≡ y .snd
Σeq₂' refl refl = refl

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

Π′ : ∀ {ℓ ℓ'} {A : Set ℓ}
  {B C : A → Set ℓ'}
  → ---------------------------------
  ((a : A) → B a → C a) → Π B → Π C
Π′ F p a = F a (p a)

postulate
  funext :
     {ℓ  ℓ' : Level}
     {A : Set ℓ}
     {B : A → Set ℓ'}
     {f g : (x : A) → B x}
     → ----------------------------
     ((x : A) → f x ≡ g x) → f ≡ g

funextDepDom : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : Set ℓ''}
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {f₀ : B a₀ → C} {f₁ : B a₁ → C}
  → (∀ b → f₀ b ≡ f₁ (subst B p b))
  → subst (λ a → B a → C) p f₀ ≡ f₁
funextDepDom refl = funext

funextDepCod : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : A → Set ℓ''}
  {a₀ a₁ : A} (p : a₀ ≡ a₁)
  {f₀ : B → C a₀} {f₁ : B → C a₁}
  → (∀ b → subst C p (f₀ b) ≡ f₁ b)
  → subst (λ a → B → C a) p f₀ ≡ f₁
funextDepCod refl = funext

----------------------------------------------------------------------
-- Isomorphism
----------------------------------------------------------------------
record _≅_ (A B : Set) : Set where
 field
  to   : A → B
  from : B → A
  inv₁ : from ∘ to ≡ id
  inv₂ : to ∘ from ≡ id

open _≅_ public
