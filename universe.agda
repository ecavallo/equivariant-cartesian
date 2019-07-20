{-

Universe of fibrant types

-}
{-# OPTIONS --rewriting #-}
module universe where

open import prelude
open import shape
open import cofprop
open import fibrations
open import Data.functions
open import Data.paths
open import Data.products
open import equivs
open import glueing
open import union

module Tiny (@♭ S : Shape) where

  postulate
    -- the value of the right adjoint on objects
    √ : {@♭ ℓ : Level} (@♭ A : Set ℓ) → Set ℓ

  module _ {@♭ ℓ ℓ' : Level} {@♭ A : Set ℓ} {@♭ B : Set ℓ'} where

    postulate
      -- right transposition across the adjunction
      R : @♭ ((⟨ S ⟩ → A) → B) → (A → √ B)

      -- left transposition across the adjunction
      L : @♭ (A → √ B) → ((⟨ S ⟩ → A) → B)

      -- right and left transposition are mutually inverse
      LR : (@♭ f : (⟨ S ⟩ → A) → B) → L (R f) ≡ f
      RL : (@♭ g : A → √ B) → R (L g) ≡ g

    {-# REWRITE LR RL #-}

  postulate
    -- one-sided naturality of right transposition
    R℘ : {@♭ ℓ ℓ' ℓ'' : Level}
      {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
      (@♭ g : A → B) (@♭ f : (⟨ S ⟩ → B) → C)
      → R (f ∘ (_∘_ g)) ≡ R f ∘ g

  -- One-sided naturality of left transposition is derivable
  L℘ : {@♭ ℓ ℓ' ℓ'' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ f : B → √ C) (@♭ g : A → B)
    →  L f ∘ _∘_ g ≡ L (f ∘ g)
  L℘ f g = cong L (R℘ g (L f))

  -- Functoriality of √ in the set argument
  √` : {@♭ ℓ ℓ' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ f : A → B) → √ A → √ B
  √` f = R (f ∘ L id)

  -- The other naturality property of right transposition
  √R : {@♭ ℓ ℓ' ℓ'' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ g : B → C) (@♭ f : (⟨ S ⟩ → A) → B)
    → √` g ∘ R f ≡ R (g ∘ f)
  √R {A = A} {B} {C = C} g f =
    trans
      (cong (R ∘ _∘_ g) (L℘ id (R f)))
      (symm (R℘ (R f) (g ∘ L id)))
  -- The other naturality property of left transposition
  L√ : {@♭ ℓ ℓ' ℓ'' : Level}
    {@♭ A : Set ℓ} {@♭ B : Set ℓ'} {@♭ C : Set ℓ''}
    (@♭ g : B → C) (@♭ f : A → √ B)
    → ---------------------
    g ∘ L f  ≡ L (√` g ∘ f)
  L√ g f = cong L (symm (√R g (L f)))

open Tiny

postulate
  ShapeIsDiscrete : ∀ {ℓ} {A : Shape → Set ℓ}
    → ((@♭ S : Shape) → A S) → ((S : Shape) → A S)

  ShapeIsDiscrete-β : ∀ {ℓ} {A : Shape → Set ℓ} (f : (@♭ S : Shape) → A S)
    (@♭ S : Shape) → ShapeIsDiscrete f S ≡ f S

  {-# REWRITE ShapeIsDiscrete-β #-}

  ShapeHomIsDiscrete : ∀ {ℓ} {@♭ S T : Shape} {A : ShapeHom S T → Set ℓ}
    → ((@♭ σ : ShapeHom S T) → A σ) → ((σ : ShapeHom S T) → A σ)

  ShapeHomIsDiscrete-β : ∀ {ℓ} {@♭ S T : Shape} {A : ShapeHom S T → Set ℓ}
    (f : (@♭ σ : ShapeHom S T) → A σ)
    (@♭ σ : ShapeHom S T) → ShapeHomIsDiscrete f σ ≡ f σ

-- Functoriality and naturality in the shape argument
module _ {@♭ S T : Shape} (@♭ σ : ShapeHom S T) where

  √ShapeHom : {@♭ ℓ : Level} {@♭ A : Set ℓ}
    → √ S A → √ T A
  √ShapeHom = R T (L S id ∘ (_∘_ ◆ ⟪ σ ⟫))

  LShapeHom : {@♭ ℓ ℓ' : Level} {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ f : A → √ S B)
    → L T (√ShapeHom ∘ f) ≡ L S f ∘ (_∘_ ◆ ⟪ σ ⟫)
  LShapeHom f =
    trans
      (cong (_∘_ ◆ (_∘_ ◆ ⟪ σ ⟫)) (L℘ S id f))
      (symm (L℘ T √ShapeHom f))

  ShapeHomR : {@♭ ℓ ℓ' : Level} {@♭ A : Set ℓ} {@♭ B : Set ℓ'}
    (@♭ g : (⟨ S ⟩ → A) → B)
    → √ShapeHom ∘ R S g ≡ R T (g ∘ (_∘_ ◆ ⟪ σ ⟫))
  ShapeHomR g =
    cong (R T) (LShapeHom (R S g))

Set* : Set₁
Set* = Σ Set id

record Span : Set₁ where
  field
    Src : Set
    Dst : Set
    Rel : Src → Dst → Set

open Span public

record Witness (D : Span) : Set₁ where
  field
    src : D .Src
    dst : D .Dst
    rel : D .Rel src dst

open Witness public

Span* : Set₁
Span* = Σ D ∈ Span , Witness D

src* : Span* → Set*
src* (D , W) = (D .Src , W .src)

dst* : Span* → Set*
dst* (D , W) = (D .Dst , W .dst)

substSpan : ∀ {ℓ} {A : Set ℓ} (D : A → Span)
  {x y : A} (p : x ≡ y)
  → Witness (D x) → Witness (D y)
substSpan D {x} p w =
  record
  { src = subst (Src ∘ D) p (w .src)
  ; dst = subst (Dst ∘ D) p (w .dst)
  ; rel = j p
  }
  where
  j : ∀ {y} (p : x ≡ y)
    → D y .Rel (subst (Src ∘ D) p (w .src)) (subst (Dst ∘ D) p (w .dst))
  j refl = w .rel

hasLifts : (S : Shape) (A : ⟨ S ⟩ → Set) → Set
hasLifts S A = ∀ r φ f x₀ → Comp S r A φ f x₀

hasVaries : (S T : Shape) (σ : ShapeHom S T) (A : ⟨ T ⟩ → Set) → Span
hasVaries S T σ A =
  record
  { Src = hasLifts T A
  ; Dst = hasLifts S (A ∘ ⟪ σ ⟫)
  ; Rel = λ cT cS → ∀ r φ f x₀ s →
    cT (⟪ σ ⟫ r) φ f x₀ .comp (⟪ σ ⟫ s) .fst ≡ cS r φ (f ◇ ⟪ σ ⟫) x₀ .comp s .fst
  }

record U : Set₁ where
  field
    El : Set
    lifts : (@♭ S : Shape) → √ S Set*
    liftsBase : (@♭ S : Shape) → √` S fst (lifts S) ≡ R S (hasLifts S) El

    varies : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) → √ T Span*
    variesBase : (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
      → √` T fst (varies S T σ) ≡ R T (hasVaries S T σ) El
    variesSrc : (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
      → √` T src* (varies S T σ) ≡ lifts T
    variesDst : (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
      → √` T dst* (varies S T σ) ≡ √ShapeHom σ (lifts S)

open U public

UExt : {A B : U} → A .El ≡ B .El → A .lifts ≡ B .lifts → A .varies ≡ B .varies → A ≡ B
UExt {A = A} {B} refl refl refl =
  cong
    (λ {(cBase , vBase , vSrc , vDst) → record
      { El = A .El
      ; lifts = A .lifts
      ; liftsBase = cBase
      ; varies = A .varies
      ; variesBase = vBase
      ; variesSrc = vSrc
      ; variesDst = vDst
      }})
    (×ext
      (funext {B = λ (@♭ _) → _} λ (@♭ S) → uipImp)
      (×ext
        (funext {B = λ (@♭ _) → _} λ (@♭ S) →
          funext {B = λ (@♭ _) → _} λ (@♭ T) →
          funext {B = λ (@♭ _) → _} λ (@♭ σ) → uipImp)
        (×ext
          (funext {B = λ (@♭ _) → _} λ (@♭ S) →
            funext {B = λ (@♭ _) → _} λ (@♭ T) →
            funext {B = λ (@♭ _) → _} λ (@♭ σ) → uipImp)
          (funext {B = λ (@♭ _) → _} λ (@♭ S) →
            funext {B = λ (@♭ _) → _} λ (@♭ T) →
            funext {B = λ (@♭ _) → _} λ (@♭ σ) → uipImp))))

fstLlifts : (@♭ S : Shape) → fst ∘ L S (λ A → A .lifts S) ≡ hasLifts S ∘ (_∘_ El)
fstLlifts S =
  trans
    (cong (L S)
      (trans
        (symm (R℘ S El (hasLifts S)))
        (funext (λ A → A .liftsBase S))))
    (L√ S fst (λ A → A .lifts S))

getLifts : (@♭ S : Shape) (C : ⟨ S ⟩ → U) → hasLifts S (El ∘ C)
getLifts S C = coe (appCong (fstLlifts S)) (L S (λ A → A .lifts S) C .snd)

Llifts : (@♭ S : Shape) (C : ⟨ S ⟩ → U)
  → L S (λ A → A .lifts S) C ≡ (hasLifts S (El ∘ C) , getLifts S C)
Llifts S C = Σext (appCong (fstLlifts S)) refl

fstLvaries : (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
  → fst ∘ L T (λ A → A .varies S T σ) ≡ hasVaries S T σ ∘ (_∘_ El)
fstLvaries S T σ =
  trans
    (cong (L T)
      (trans
        (symm (R℘ T El (hasVaries S T σ)))
        (funext (λ A → A .variesBase S T σ))))
    (L√ T fst (λ A → A .varies S T σ))

srcLvaries : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U)
  → src* (L T (λ A → A .varies S T σ) C) ≡ (hasLifts T (El ∘ C) , getLifts T C)
srcLvaries S T σ C =
  appCong
    (trans
      (trans
        (funext (Llifts T))
        (cong (L T) (funext (λ A → A .variesSrc S T σ))))
      (L√ T src* (λ A → A .varies S T σ)))

dstLvaries : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U)
  → dst* (L T (λ A → A .varies S T σ) C) ≡ (hasLifts S (El ∘ C ∘ ⟪ σ ⟫) , getLifts S (C ∘ ⟪ σ ⟫))
dstLvaries S T σ C =
  appCong
    {f = λ C → dst* (L T (λ A → A .varies S T σ) C)}
    {g = λ C → (hasLifts S (El ∘ C ∘ ⟪ σ ⟫) , getLifts S (C ∘ ⟪ σ ⟫))}
    (trans
      (trans
        (trans
          (cong (_∘_ ◆ (_∘_ ◆ ⟪ σ ⟫)) (funext (Llifts S)))
          (LShapeHom σ (λ A → A .lifts S)))
        (cong (L T) (funext (λ A → A .variesDst S T σ))))
      (L√ T dst* (λ A → A .varies S T σ)))

getVaries : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U)
  → hasVaries S T σ (El ∘ C) .Rel (getLifts T C) (getLifts S (C ∘ ⟪ σ ⟫))
getVaries S T σ C =
  subst
    (uncurry (hasVaries S T σ (El ∘ C) .Rel))
    (×ext
       (trans
         (Σeq₂' (srcLvaries S T σ C) (cong (λ D → D C .Src) (fstLvaries S T σ)))
         (substCongAssoc id (λ D → D C .Src) (fstLvaries S T σ) _))
       (trans
         (Σeq₂' (dstLvaries S T σ C) (cong (λ D → D C .Dst) (fstLvaries S T σ)))
         (substCongAssoc id (λ D → D C .Dst) (fstLvaries S T σ) _)))
    (substSpan (λ F → F C) (fstLvaries S T σ) (L T (λ A → A .varies S T σ) C .snd) .rel)

υ : isFib El
υ .lift =
  ShapeIsDiscrete λ (@♭ S) → λ r C → getLifts S C r
υ .vary =
  ShapeIsDiscrete λ (@♭ S) →
  ShapeIsDiscrete λ (@♭ T) →
  ShapeHomIsDiscrete λ (@♭ σ) →
  λ r C → getVaries S T σ C r

decode : ∀ {ℓ} {Γ : Set ℓ} → (Γ → U) → Fib Γ
decode = reindex' (El , υ)

encode : ∀ {@♭ ℓ} {@♭ Γ : Set ℓ} → @♭ (Fib Γ) → (Γ → U)
encode {Γ = Γ} (A , α) =
  λ x →
  record
  { El = A x

  ; lifts = λ (@♭ S) → Rl S x
  ; liftsBase = λ (@♭ S) →
    appCong (trans (R℘ S A (hasLifts S)) (cong (R S) (symm (L√ S fst (Rl S)))))
  ; varies = λ (@♭ S T σ) → Rv S T σ x
  ; variesBase = λ (@♭ S T σ) →
    appCong (trans (R℘ T A (hasVaries S T σ)) (cong (R T) (symm (L√ T fst (Rv S T σ)))))
  ; variesSrc = λ (@♭ S T σ) →
    appCong
      (cong (R T)
        {x = L T (R T (λ x → (src* ∘ L T id) x) ∘ Rv S T σ)}
        (symm (L√ T src* (Rv S T σ))))
  ; variesDst = λ (@♭ S T σ) →
    appCong
      (trans
        (symm (ShapeHomR σ (l S)))
        (cong (R T)
          {x = L T (R T (λ x → (dst* ∘ L T id) x) ∘ Rv S T σ)}
          (symm (L√ T dst* (Rv S T σ)))))
  }
  where
  l : (@♭ S : Shape) → (⟨ S ⟩ → Γ) → Set*
  l S p = (hasLifts S (A ∘ p) , λ r → α .lift S r p)

  Rl : (@♭ S : Shape) → Γ → √ S Set*
  Rl S = R S (l S)

  v : ∀ (@♭ S T) (σ : ShapeHom S T) → (⟨ T ⟩ → Γ) → Span*
  v S T σ p =
    ( hasVaries S T σ (A ∘ p)
    , record
      { src = λ r → α .lift T r p
      ; dst = λ r → α .lift S r (p ∘ ⟪ σ ⟫)
      ; rel = λ r → α .vary S T σ r p
      }
    )

  Rv : ∀ (@♭ S T) (@♭ σ : ShapeHom S T) → Γ → √ T Span*
  Rv S T σ = R T (v S T σ)

decodeEncode : {@♭ ℓ : Level} {@♭ Γ : Set ℓ} (@♭ Aα : Fib Γ) → decode (encode Aα) ≡ Aα
decodeEncode {Γ = Γ} Aα =
  Σext refl
    (fibExt
      (ShapeIsDiscrete λ (@♭ S) r p φ f x₀ s →
        cong
          {A = Σ C ∈ Set* , C .fst ≡ hasLifts S (A ∘ p)}
          (λ {(C , eq) → coe eq (C .snd) r φ f x₀ .comp s .fst})
          {x = _ , appCong (fstLlifts S)}
          {y = _ , refl}
          (Σext (lemma S p) uipImp)))
  where
  A = Aα .fst
  α = Aα .snd

  lemma : (@♭ S : Shape) (p : ⟨ S ⟩ → Γ)
    → L S (λ C → C .lifts S) (encode Aα ∘ p) ≡ (hasLifts S (A ∘ p) , λ r → α .lift S r p)
  lemma S p =
    trans
      (appCong
        (L℘ S id (R S {B = Set*} (λ p → hasLifts S (A ∘ p) , λ r → α .lift S r p))))
      (appCong (symm (L℘ S id (λ C → C .lifts S))))

