{-

Constructing a universe that classifies fibrations

-}
{-# OPTIONS --rewriting #-}
module universe.core where

open import prelude
open import axioms
open import fibration.fibration

private variable ℓ ℓ' : Level

open Tiny

record Span ℓ : Type (lsuc ℓ) where
  field
    Src : Type ℓ
    Dst : Type ℓ
    Rel : Src → Dst → Type ℓ

open Span public

record Witness {ℓ} (D : Span ℓ) : Type ℓ where
  constructor witness
  field
    src : D .Src
    dst : D .Dst
    rel : D .Rel src dst

open Witness public

Span* : ∀ ℓ → Type (lsuc ℓ)
Span* ℓ = Σ D ∈ Span ℓ , Witness D

src* : Span* ℓ → Type* ℓ
src* (D , W) = (D .Src , W .src)

dst* : Span* ℓ → Type* ℓ
dst* (D , W) = (D .Dst , W .dst)

hasLifts : (S : Shape) (A : ⟨ S ⟩ → Type ℓ) → Type ℓ
hasLifts S A = ∀ r (box : OpenBox S r A) → Filler box

hasVaries : (S T : Shape) (σ : ShapeHom S T) (A : ⟨ T ⟩ → Type ℓ) → Span ℓ
hasVaries S T σ A .Src = hasLifts T A
hasVaries S T σ A .Dst = hasLifts S (A ∘ ⟪ σ ⟫)
hasVaries S T σ A .Rel cT cS =
  ∀ r box s →
  cT (⟪ σ ⟫ r) box .fill (⟪ σ ⟫ s) .out ≡ cS r (reshapeBox σ box) .fill s .out

------------------------------------------------------------------------------------------
-- Definition of the universe
------------------------------------------------------------------------------------------

record U (@♭ ℓ) : Type (lsuc ℓ) where
  field
    El : Type ℓ
    lifts : (@♭ S : Shape) → √ S (Type* ℓ)
    liftsBase : (@♭ S : Shape) → √` S fst (lifts S) ≡ R S (hasLifts S) El

    varies : (@♭ S T : Shape) (@♭ σ : ShapeHom S T) → √ T (Span* ℓ)
    variesBase : (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
      → √` T fst (varies S T σ) ≡ R T (hasVaries S T σ) El
    variesSrc : (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
      → √` T src* (varies S T σ) ≡ lifts T
    variesDst : (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
      → √` T dst* (varies S T σ) ≡ √ShapeHom σ (lifts S)

open U public

UExt : ∀ {@♭ ℓ} {A B : U ℓ}
  → A .El ≡ B .El → A .lifts ≡ B .lifts → A .varies ≡ B .varies
  → A ≡ B
UExt {A = A} refl refl refl =
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
      (funext♭ λ S → uipImp)
      (×ext
        (funext♭ λ S → funext♭ λ T → funext♭ λ σ → uipImp)
        (×ext
          (funext♭ λ S → funext♭ λ T → funext♭ λ σ → uipImp)
          (funext♭ λ S → funext♭ λ T → funext♭ λ σ → uipImp))))

------------------------------------------------------------------------------------------
-- Extracting lifts from a map into U
------------------------------------------------------------------------------------------

fstLlifts : ∀ {@♭ ℓ} (@♭ S : Shape) →
  fst ∘ L S {A = U ℓ} (λ A → A .lifts S) ≡ hasLifts S ∘ (El ∘_)
fstLlifts S =
  L√ S fst (λ A → A .lifts S)
  ∙ cong♭ (L S) (funext (λ A → A .liftsBase S) ∙ sym (R℘ S El (hasLifts S)))

getLifts : ∀ {@♭ ℓ} (@♭ S : Shape) (C : ⟨ S ⟩ → U ℓ) → hasLifts S (El ∘ C)
getLifts S C = coe (appCong (fstLlifts S)) (L S (λ A → A .lifts S) C .snd)

Llifts : ∀ {@♭ ℓ} (@♭ S : Shape) (C : ⟨ S ⟩ → U ℓ)
  → L S (λ A → A .lifts S) C ≡ (hasLifts S (El ∘ C) , getLifts S C)
Llifts S C = Σext (appCong (fstLlifts S)) refl

------------------------------------------------------------------------------------------
-- Extracting equivariance from a map into U
------------------------------------------------------------------------------------------

fstLvaries : ∀ {@♭ ℓ} (@♭ S T : Shape) (@♭ σ : ShapeHom S T)
  → fst ∘ L T {A = U ℓ} (λ A → A .varies S T σ) ≡ hasVaries S T σ ∘ (El ∘_)
fstLvaries S T σ =
  L√ T fst (λ A → A .varies S T σ)
  ∙ cong♭ (L T) (funext (λ A → A .variesBase S T σ) ∙ sym (R℘ T El (hasVaries S T σ)))

srcLvaries : ∀ {@♭ ℓ} (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U ℓ)
  → src* (L T (λ A → A .varies S T σ) C) ≡ (hasLifts T (El ∘ C) , getLifts T C)
srcLvaries S T σ C =
  appCong
    (L√ T src* (λ A → A .varies S T σ)
      ∙ cong♭ (L T) (funext (λ A → A .variesSrc S T σ))
      ∙ funext (Llifts T))

dstLvaries : ∀ {@♭ ℓ} (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U ℓ)
  → dst* (L T (λ A → A .varies S T σ) C)
    ≡ (hasLifts S (El ∘ C ∘ ⟪ σ ⟫) , getLifts S (C ∘ ⟪ σ ⟫))
dstLvaries S T σ C =
  appCong
    (L√ T dst* (λ A → A .varies S T σ)
      ∙ cong♭ (L T) (funext (λ A → A .variesDst S T σ))
      ∙ LShapeHom σ (λ A → A .lifts S)
      ∙ cong (_∘ (_∘ ⟪ σ ⟫)) (funext (Llifts S)))

substSpan : {A : Type ℓ} (D : A → Span ℓ')
  {x y : A} (p : x ≡ y)
  → Witness (D x) → Witness (D y)
substSpan D p w .src = subst (Src ∘ D) p (w .src)
substSpan D p w .dst = subst (Dst ∘ D) p (w .dst)
substSpan D refl w .rel = w .rel

getVaries : ∀ {@♭ ℓ} (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U ℓ)
  → Witness (hasVaries S T σ (El ∘ C))
getVaries S T σ C .src = getLifts T C
getVaries S T σ C .dst = getLifts S (C ∘ ⟪ σ ⟫)
getVaries S T σ C .rel =
  subst
    (uncurry (hasVaries S T σ (El ∘ C) .Rel))
    (×ext
       (substCongAssoc id (λ D → D C .Src) (fstLvaries S T σ) _
         ∙ Σeq₂ (srcLvaries S T σ C) (cong (λ D → D C .Src) (fstLvaries S T σ)))
       (substCongAssoc id (λ D → D C .Dst) (fstLvaries S T σ) _
         ∙ Σeq₂ (dstLvaries S T σ C) (cong (λ D → D C .Dst) (fstLvaries S T σ))))
    (substSpan (λ F → F C) (fstLvaries S T σ) (L T (λ A → A .varies S T σ) C .snd) .rel)

Lvaries : ∀ {@♭ ℓ} (@♭ S T : Shape) (@♭ σ : ShapeHom S T) (C : ⟨ T ⟩ → U ℓ)
  → L T (λ A → A .varies S T σ) C ≡ (hasVaries S T σ (El ∘ C) , getVaries S T σ C)
Lvaries S T σ C =
  Σext
    (appCong (fstLvaries S T σ))
    (witnessExtLemma
      (appCong (fstLvaries S T σ))
      (srcLvaries S T σ C)
      (dstLvaries S T σ C)
      (λ _ _ → funext λ r → funext λ box → funext λ s → uipImp))
  where
  witnessExtLemma : {D D' : Span _} (p : D ≡ D')
    {w : Witness D} {w' : Witness D'}
    (q : src* (D , w) ≡ src* (D' , w'))
    (q' : dst* (D , w) ≡ dst* (D' , w'))
    → (∀ {a b} → (r r' : D' .Rel a b) → r ≡ r')
    → subst Witness p w ≡ w'
  witnessExtLemma refl refl refl prop =
    cong (witness _ _) (prop _ _)

------------------------------------------------------------------------------------------
-- El : U → Type is a fibration
------------------------------------------------------------------------------------------

υ : ∀ {@♭ ℓ} → isFib (El {ℓ})
υ .lift =
  ShapeIsDiscrete λ (@♭ S) → λ r C → getLifts S C r
υ .vary =
  ShapeIsDiscrete λ (@♭ S) →
  ShapeIsDiscrete λ (@♭ T) →
  ShapeHomIsDiscrete λ (@♭ σ) →
  λ r C → getVaries S T σ C .rel r

decode : ∀ {@♭ ℓ'} {Γ : Type ℓ} → (Γ → U ℓ') → Fib ℓ' Γ
decode = reindexFib (El , υ)

------------------------------------------------------------------------------------------
-- Any fibration induces a map into U
------------------------------------------------------------------------------------------

FibLifts : {Γ : Type ℓ} → Fib ℓ' Γ
  → (@♭ S : Shape) → (⟨ S ⟩ → Γ) → Type* ℓ'
FibLifts (A , α) S p = (hasLifts S (A ∘ p) , λ r → α .lift S r p)

FibVaries : {Γ : Type ℓ} → Fib ℓ' Γ
  → ∀ (@♭ S T) (σ : ShapeHom S T) → (⟨ T ⟩ → Γ) → Span* ℓ'
FibVaries (A , α) S T σ p .fst =
  hasVaries S T σ (A ∘ p)
FibVaries (A , α) S T σ p .snd .src r = α .lift T r p
FibVaries (A , α) S T σ p .snd .dst r = α .lift S r (p ∘ ⟪ σ ⟫)
FibVaries (A , α) S T σ p .snd .rel r = α .vary S T σ r p

encode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} → @♭ (Fib ℓ' Γ) → (Γ → U ℓ')
encode {ℓ' = ℓ'} {Γ} Aα = encoding
  where
  Rl : (@♭ S : Shape) → Γ → √ S (Type* ℓ')
  Rl S = R S (FibLifts Aα S)

  Rv : ∀ (@♭ S T) (@♭ σ : ShapeHom S T) → Γ → √ T (Span* ℓ')
  Rv S T σ = R T (FibVaries Aα S T σ)

  encoding : Γ → U ℓ'
  encoding x .El = Aα .fst x
  encoding x .lifts S = Rl S x
  encoding x .liftsBase S =
    appCong (cong♭ (R S) (sym (L√ S fst (Rl S))) ∙ R℘ S (Aα .fst) (hasLifts S))
  encoding x .varies S T σ = Rv S T σ x
  encoding x .variesBase S T σ =
    appCong (cong♭ (R T) (sym (L√ T fst (Rv S T σ))) ∙ R℘ T (Aα .fst) (hasVaries S T σ))
  encoding x .variesSrc S T σ =
    appCong (cong♭ (R T) (sym (L√ T src* (Rv S T σ))))
  encoding x .variesDst S T σ =
    appCong
      (cong♭ (R T) (sym (L√ T dst* (Rv S T σ))) ∙ sym (ShapeHomR σ (FibLifts Aα S)))

------------------------------------------------------------------------------------------
-- Inverse conditions for the correspondence between Fib Γ and Γ → U
------------------------------------------------------------------------------------------

decodeEncode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ Aα : Fib ℓ' Γ)
  → decode (encode Aα) ≡ Aα
decodeEncode Aα =
  Σext refl
    (isFibExt
      (ShapeIsDiscrete λ (@♭ S) r p box s →
        cong
          {A = Σ C ∈ Type* _ , C .fst ≡ hasLifts S (A ∘ p)}
          (λ {(C , eq) → coe eq (C .snd) r box .fill s .out})
          {x = _ , appCong (fstLlifts S)}
          {y = _ , refl}
          (Σext (lemma S p) uipImp)))
  where
  A = Aα .fst
  α = Aα .snd

  lemma : (@♭ S : Shape) (p : ⟨ S ⟩ → _)
    → L S (λ C → C .lifts S) (encode Aα ∘ p) ≡ (hasLifts S (A ∘ p) , λ r → α .lift S r p)
  lemma S p =
    appCong (sym (L℘ S id (λ C → C .lifts S)))
    ∙ appCong (L℘ S id (R S {B = Type* _} (FibLifts Aα S)))

encodeReindexFib : ∀ {@♭ ℓ ℓ' ℓ''} {@♭ Δ : Type ℓ} {@♭ Γ : Type ℓ'}
  (@♭ Aα : Fib ℓ'' Γ) (@♭ ρ : Δ → Γ) (x : Δ)
  → encode (reindexFib Aα ρ) x ≡ encode Aα (ρ x)
encodeReindexFib Aα ρ x =
  UExt
    refl
    (funext♭ λ S →
      appCong (R℘ S ρ (FibLifts Aα S)))
    (funext♭ λ S → funext♭ λ T → funext♭ λ σ →
      appCong (R℘ T ρ (FibVaries Aα S T σ)))

encodeEl : ∀ {@♭ ℓ} → (C : U ℓ) → encode (El , υ) C ≡ C
encodeEl C =
  UExt
    refl
    (funext♭ λ S →
      appCong
        (cong♭ (R S)
          {y = L S (λ D → D .lifts S)}
          (sym (funext (Llifts S)))))
    (funext♭ λ S → funext♭ λ T → funext♭ λ σ →
      appCong
        (cong♭ (R T)
          (sym (funext λ C →
            Lvaries S T σ C
            ∙ cong
                (λ w →
                  ( hasVaries S T σ (El ∘ C)
                  , witness (getLifts T C) (getLifts S (C ∘ ⟪ σ ⟫)) w
                  ))
                (funext λ r → funext λ box → funext λ s → uipImp)))))

encodeDecode : ∀ {@♭ ℓ ℓ'} {@♭ Γ : Type ℓ} (@♭ C : Γ → U ℓ') → encode (decode C) ≡ C
encodeDecode C = funext λ x →
  encodeReindexFib (El , υ) C x ∙ encodeEl (C x)
