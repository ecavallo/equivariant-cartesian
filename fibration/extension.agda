{-

Fibration extension property

-}
{-# OPTIONS --rewriting #-}
module fibration.extension where

open import prelude
open import axioms
open import fibration.fibration
open import type-formers.sigma
open import type-formers.union
open import type-formers.equivs
open import glueing

module Box {ℓ ℓ'} {Γ : Set ℓ}
  (S : Shape) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib ℓ' (Γ ,[ φ ] × ⟨ S ⟩))
  (X₀ : Fib ℓ' Γ) (match : reindexFib F (λ {(x , u) → (x , u) , r x}) ≡ reindexFib X₀ fst)
  (s : Γ → ⟨ S ⟩)
  where

  ats : Γ ,[ φ ] → Γ ,[ φ ] × ⟨ S ⟩
  ats (x , u) = (x , u) , s x

  fst' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} → Σ Γ (A ×' B) → Σ Γ A
  fst' (x , a , b) = (x , a)

  -- We want to isolate the parts that depend essentially on r and s, so that we can
  -- prove equivariance more easily. Those parts are parameters to this module.
  module Template (ψ : Γ → CofProp)
    (ψMatch : reindexFib F (ats ∘ fst') ≡ reindexFib X₀ fst)
    (φEquiv : ∀ x → (u : [ φ x ]) → Equiv (F .fst ((x , u) , s x)) (X₀ .fst x))
    (equivMatch : ∀ x → (u : [ φ x ]) (v : [ ψ x ]) →
      subst (Equiv ◆ X₀ .fst x) (cong (λ Bβ → Bβ .fst (x , u , v)) ψMatch) (φEquiv x u)
      ≡ idEquiv (reindexFib X₀ (λ _ → x) .snd))
    where

    module F = FibUnion φ ψ (reindexFib F ats) (reindexFib X₀ fst) ψMatch
    open F public

    equiv : Π (Equiv' (fib .fst) (X₀ .fst ∘ fst))
    equiv = uncurry λ x →
      ∨-elim (φ x) (ψ x) _
        (λ u →
          subst (Equiv ◆ X₀ .fst x)
            (cong (λ Bβ → Bβ .fst (x , u)) (sym left))
            (φEquiv x u))
        (λ v →
          subst (Equiv ◆ X₀ .fst x)
            (cong (λ Bβ → Bβ .fst (x , v)) (sym right))
            (idEquiv (reindexFib X₀ (λ _ → x) .snd)))
        (λ u v →
          substCongAssoc (Equiv ◆ X₀ .fst x) (curry (fib .fst) x) (trunc _ _) _
          ∙
          sym
            (substTrans (Equiv ◆ X₀ .fst x)
              (cong (curry (fib .fst) x) (trunc _ _))
              (cong (λ Bβ → Bβ .fst (x , u)) (sym left)))
          ∙
          adjustSubstEq (Equiv ◆ X₀ .fst x)
            (cong (λ Bβ → Bβ .fst (x , u , v)) ψMatch)
              refl
              (cong (λ Bβ → Bβ .fst (x , u)) (sym left) ∙ cong (curry (fib .fst) x) (trunc _ _))
              (cong (λ Bβ → Bβ .fst (x , v)) (sym right))
              (equivMatch x u v))

  rsMatch : reindexFib F (ats ∘ fst') ≡ reindexFib X₀ fst
  rsMatch =
    cong (reindexFib F) (funext λ {(x , u , eq) → Σext refl (sym eq)})
    ∙ cong (reindexFib ◆ fst') match

  rsEquiv : ∀ x → (u : [ φ x ]) → Equiv (F .fst ((x , u) , s x)) (X₀ .fst x)
  rsEquiv x u =
    subst (Equiv (F .fst ((x , u) , s x)))
      (cong (λ Bβ → Bβ .fst (x , u)) match)
      (coerceEquiv S (reindexFib F (λ i → ((x , u) , i)) .snd) (s x) (r x))

  rsEquivMatch : (x : Γ) (u : [ φ x ]) (eq : r x ≡ s x) →
    subst (Equiv ◆ X₀ .fst x) (cong (λ Bβ → Bβ .fst (x , u , eq)) rsMatch) (rsEquiv x u)
    ≡ idEquiv (reindexFib X₀ (λ _ → x) .snd)
  rsEquivMatch x u eq =
    lemma
      (reindexFib F (λ _ → (x , u) , r x) .snd)
      (reindexFib X₀ (λ _ → x) .snd)
      (cong (λ Bβ → Bβ .fst (x , u , eq)) rsMatch)
      (cong (λ t → F .fst ((x , u) , t)) (sym eq))
      (cong (λ Bβ → Bβ .fst (x , u)) match)
      (Σeq₂
        (cong (λ Bβ → (Bβ .fst (x , u) , reindexFib Bβ (λ _ → (x , u)) .snd)) match)
        (cong (λ Bβ → Bβ .fst (x , u)) match))
      (coerceEquiv S (reindexFib F (λ i → ((x , u) , i)) .snd) (s x) (r x))
      (sym
        (substCongAssoc
          (Equiv ◆ fst (reindexFib F (λ _ → (x , u) , r x)) tt)
            (λ t → F .fst ((x , u) , t))
            (sym eq)
            (coerceEquiv S (reindexFib F (λ i → (x , u) , i) .snd) (s x) (r x)))
       ∙
       congdep
         (λ t → coerceEquiv S (reindexFib F (λ i → (x , u) , i) .snd) t (r x))
         (sym eq)
       ∙
       coerceEquivCap S (reindexFib F (λ i → ((x , u) , i)) .snd) (r x))
    where
    lemma : {A B G : Set ℓ'}
      (β : isFib (λ _ → B)) (γ : isFib (λ _ → G))
      (eqAG : A ≡ G) (eqAB : A ≡ B) (eqBG : B ≡ G)
      (eqβγ : subst (λ D → isFib (λ _ → D)) eqBG β ≡ γ)
      (e : Equiv A B)
      → subst (Equiv ◆ B) eqAB e ≡ idEquiv β
      → subst (Equiv ◆ G) eqAG (subst (Equiv A) eqBG e) ≡ idEquiv γ
    lemma β γ refl refl refl refl e eq = eq

  open Template (λ x → S ∋ r x ≈ s x) rsMatch rsEquiv rsEquivMatch public

module _ {ℓ ℓ'} {Γ : Set ℓ}
  (S : Shape) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib ℓ' (Γ ,[ φ ] × ⟨ S ⟩))
  (X₀ : Fib ℓ' Γ) (match : reindexFib F (λ {(x , u) → (x , u) , r x}) ≡ reindexFib X₀ fst)
  where

  module _ (s : Γ → ⟨ S ⟩) where

    open Box S r φ F X₀ match s

    LargeComp : Fib ℓ' Γ
    LargeComp = FibSGlue (λ x → φ x ∨ S ∋ r x ≈ s x) fib X₀ equiv

    LargeCompMatch : reindexFib F ats ≡ reindexFib LargeComp fst
    LargeCompMatch =
      sym left
      ∙
      cong
        (reindexFib ◆ inl' φ (λ x → S ∋ r x ≈ s x))
        (FibSGlueStrictness (λ x → φ x ∨ S ∋ r x ≈ s x) fib X₀ equiv)

  LargeCap : LargeComp r ≡ X₀
  LargeCap =
    cong (reindexFib ◆ (inr' φ (λ x → S ∋ r x ≈ r x) ∘ f₀))
      (sym (FibSGlueStrictness (λ x → φ x ∨ S ∋ r x ≈ r x) fib X₀ equiv))
    ∙
    cong (reindexFib ◆ f₀) right
    where
    open Box S r φ F X₀ match r

    f₀ : Γ → Γ ,[ (λ x → S ∋ r x ≈ r x) ]
    f₀ x = x , refl

module _ {ℓ ℓ'} {Γ : Set ℓ}
  (S T : Shape) (σ : ShapeHom S T) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib ℓ' (Γ ,[ φ ] × ⟨ T ⟩))
  (X₀ : Fib ℓ' Γ) (match : reindexFib F (λ {(x , u) → (x , u) , ⟪ σ ⟫ (r x)}) ≡ reindexFib X₀ fst)
  (s : Γ → ⟨ S ⟩)
  where

  module S = Box S r φ (reindexFib F (id× ⟪ σ ⟫)) X₀ match s
  module T = Box T (⟪ σ ⟫ ∘ r) φ F X₀ match (⟪ σ ⟫ ∘ s)

  varyEquiv : T.rsEquiv ≡ S.rsEquiv
  varyEquiv = funext λ x → funext λ u →
    cong
      (subst (Equiv (F .fst ((x , u) , ⟪ σ ⟫ (s x)))) (cong (λ Bβ → Bβ .fst (x , u)) match))
      (coerceEquivVary S T σ (reindexFib F (λ i → (x , u) , i) .snd) (s x) (r x))

  LargeVary
    : LargeComp T (⟪ σ ⟫ ∘ r) φ F X₀ match (⟪ σ ⟫ ∘ s)
      ≡ LargeComp S r φ (reindexFib F (id× ⟪ σ ⟫)) X₀ match s
  LargeVary =
    congΣ
      (λ ((ψ , ψMatch) , φEquiv) equivMatch →
        FibSGlue (λ x → φ x ∨ ψ x)
          (S.Template.fib ψ ψMatch φEquiv equivMatch)
          X₀
          (S.Template.equiv ψ ψMatch φEquiv equivMatch))
      {x' = T.rsEquivMatch}
      {y' = S.rsEquivMatch}
      (×ext
        (Σext (funext λ x → ≈Equivariant σ (r x) (s x)) uipImp)
        varyEquiv)
      (funext λ x → funext λ u → funext λ v → uipImp)

-- EC: TODO stability of FEP under substitution in the context Γ
