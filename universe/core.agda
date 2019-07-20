{-

Constructing a universe that classifies fibrations

-}
{-# OPTIONS --rewriting #-}
module universe.core where

open import prelude
open import shape
open import cofprop
open import fibrations

open import universe.axioms

open Tiny

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

----------------------------------------------------------------------
-- Definition of the universe
----------------------------------------------------------------------
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

----------------------------------------------------------------------
-- Extracting lifts from a map into U
----------------------------------------------------------------------
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

----------------------------------------------------------------------
-- Extracting equivariance from a map into U
----------------------------------------------------------------------
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

getVaries : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U)
  → Witness (hasVaries S T σ (El ∘ C))
getVaries S T σ C =
  record
  { src = getLifts T C
  ; dst = getLifts S (C ∘ ⟪ σ ⟫)
  ; rel =
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
  }

Lvaries : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U)
  → L T (λ A → A .varies S T σ) C ≡ (hasVaries S T σ (El ∘ C) , getVaries S T σ C)
Lvaries S T σ C =
  Σext
    (appCong (fstLvaries S T σ))
    (witnessExtLemma
      (appCong (fstLvaries S T σ))
      (srcLvaries S T σ C)
      (dstLvaries S T σ C)
      (λ _ _ →
        funext λ r → funext λ φ → funext λ f →
        funext λ x₀ → funext λ s → uipImp))
  where
  witnessExtLemma : {D D' : Span} (p : D ≡ D')
    {w : Witness D} {w' : Witness D'}
    (q : src* (D , w) ≡ src* (D' , w'))
    (q' : dst* (D , w) ≡ dst* (D' , w'))
    → (∀ {a b} → (r r' : D' .Rel a b) → r ≡ r')
    → subst Witness p w ≡ w'
  witnessExtLemma refl refl refl prop =
    cong
      (λ r → record {src = _; dst = _; rel = r})
      (prop _ _)

----------------------------------------------------------------------
-- El : U → Set is a fibration
----------------------------------------------------------------------
υ : isFib El
υ .lift =
  ShapeIsDiscrete λ (@♭ S) → λ r C → getLifts S C r
υ .vary =
  ShapeIsDiscrete λ (@♭ S) →
  ShapeIsDiscrete λ (@♭ T) →
  ShapeHomIsDiscrete λ (@♭ σ) →
  λ r C → getVaries S T σ C .rel r

decode : ∀ {ℓ} {Γ : Set ℓ} → (Γ → U) → Fib Γ
decode = reindex' (El , υ)

----------------------------------------------------------------------
-- Any fibration induces a map into U
----------------------------------------------------------------------
FibLifts : ∀ {ℓ} {Γ : Set ℓ} → Fib Γ
  → (@♭ S : Shape) → (⟨ S ⟩ → Γ) → Set*
FibLifts (A , α) S p = (hasLifts S (A ∘ p) , λ r → α .lift S r p)

FibVaries : ∀ {ℓ} {Γ : Set ℓ} → Fib Γ
  → ∀ (@♭ S T) (σ : ShapeHom S T) → (⟨ T ⟩ → Γ) → Span*
FibVaries (A , α) S T σ p =
  ( hasVaries S T σ (A ∘ p)
  , record
    { src = λ r → α .lift T r p
    ; dst = λ r → α .lift S r (p ∘ ⟪ σ ⟫)
    ; rel = λ r → α .vary S T σ r p
    }
  )

encode : ∀ {@♭ ℓ} {@♭ Γ : Set ℓ} → @♭ (Fib Γ) → (Γ → U)
encode {Γ = Γ} Aα =
  λ x →
  record
  { El = Aα .fst x
  ; lifts = λ (@♭ S) → Rl S x
  ; liftsBase = λ (@♭ S) →
    appCong (trans (R℘ S (Aα .fst) (hasLifts S)) (cong (R S) (symm (L√ S fst (Rl S)))))
  ; varies = λ (@♭ S T σ) → Rv S T σ x
  ; variesBase = λ (@♭ S T σ) →
    appCong (trans (R℘ T (Aα .fst) (hasVaries S T σ)) (cong (R T) (symm (L√ T fst (Rv S T σ)))))
  ; variesSrc = λ (@♭ S T σ) →
    appCong
      (cong (R T)
        {x = L T (R T (λ x → (src* ∘ L T id) x) ∘ Rv S T σ)}
        (symm (L√ T src* (Rv S T σ))))
  ; variesDst = λ (@♭ S T σ) →
    appCong
      (trans
        (symm (ShapeHomR σ (FibLifts Aα S)))
        (cong (R T)
          {x = L T (R T (λ x → (dst* ∘ L T id) x) ∘ Rv S T σ)}
          (symm (L√ T dst* (Rv S T σ)))))
  }
  where
  Rl : (@♭ S : Shape) → Γ → √ S Set*
  Rl S = R S (FibLifts Aα S)

  Rv : ∀ (@♭ S T) (@♭ σ : ShapeHom S T) → Γ → √ T Span*
  Rv S T σ = R T (FibVaries Aα S T σ)

----------------------------------------------------------------------
-- Inverse conditions for the correspondence between Fib Γ and Γ → U
----------------------------------------------------------------------
decodeEncode : ∀ {@♭ ℓ} {@♭ Γ : Set ℓ} (@♭ Aα : Fib Γ) → decode (encode Aα) ≡ Aα
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
        (L℘ S id (R S {B = Set*} (FibLifts (A , α) S))))
      (appCong (symm (L℘ S id (λ C → C .lifts S))))

encodeReindex' : ∀ {@♭ ℓ ℓ'} {@♭ Δ : Set ℓ} {@♭ Γ : Set ℓ'}
  (@♭ Aα : Fib Γ) (@♭ ρ : Δ → Γ) (x : Δ)
  → encode (reindex' Aα ρ) x ≡ encode Aα (ρ x)
encodeReindex' {Γ = Γ} Aα ρ x =
  UExt
    refl
    (funext {B = λ (@♭ _) → _} λ (@♭ S) →
      appCong (R℘ S {C = Set*} ρ (FibLifts Aα S)))
    (funext {B = λ (@♭ _) → _} λ (@♭ S) →
      funext {B = λ (@♭ _) → _} λ (@♭ T) →
      funext {B = λ (@♭ _) → _} λ (@♭ σ) →
      appCong (R℘ T {C = Span*} ρ (FibVaries Aα S T σ)))

encodeEl : (C : U) → encode (El , υ) C ≡ C
encodeEl C =
  UExt
    refl
    (funext {B = λ (@♭ _) → _} λ (@♭ S) →
      appCong
        (cong (R S)
          {y = L S (λ D → D .lifts S)}
          (symm (funext (Llifts S)))))
    (funext {B = λ (@♭ _) → _} λ (@♭ S) →
      funext {B = λ (@♭ _) → _} λ (@♭ T) →
      funext {B = λ (@♭ _) → _} λ (@♭ σ) →
      appCong
        (cong (R T)
          {x = FibVaries (El , υ) S T σ}
          {y = L T (λ D → D .varies S T σ)}
          (symm (funext λ C → trans (lemma S T σ C) (Lvaries S T σ C)))))
  where
  -- not sure why this isn't reflexive
  lemma : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U)
    → (hasVaries S T σ (El ∘ C) , getVaries S T σ C) ≡ FibVaries (El , υ) S T σ C
  lemma S T σ C =
    cong
      (λ w →
        ( hasVaries S T σ (El ∘ C)
        , record {src = getLifts T C; dst = getLifts S (C ∘ ⟪ σ ⟫); rel = w}
        ))
      (funext λ r → funext λ φ → funext λ f → funext λ x₀ → funext λ s →
        uipImp)
        
encodeDecode : ∀ {@♭ ℓ} {@♭ Γ : Set ℓ} (@♭ C : Γ → U) → encode (decode C) ≡ C
encodeDecode {Γ = Γ} C = funext λ x →
  trans
    (encodeEl (C x))
    (encodeReindex' (El , υ) C x)
