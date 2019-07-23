{-

Fibration extension property

-}
{-# OPTIONS --rewriting #-}
module fibration-extension where

open import prelude
open import axioms
open import fibrations
open import equivs
open import glueing
open import type-formers.products
open import type-formers.union

module Box {ℓ ℓ'} {Γ : Set ℓ}
  (S : Shape) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib ℓ' (res Γ φ × ⟨ S ⟩))
  (X₀ : Fib ℓ' Γ) (match : reindex' F (λ {(x , u) → (x , u) , r x}) ≡ reindex' X₀ fst)
  (s : Γ → ⟨ S ⟩)
  where

  ats : res Γ φ → res Γ φ × ⟨ S ⟩
  ats (x , u) = (x , u) , s x

  fst' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} → Σ Γ (A ×' B) → Σ Γ A
  fst' (x , a , b) = (x , a)

  -- We want to isolate the parts that depend essentially on r and s, so that we can
  -- prove equivariance more easily. Those parts are parameters to this module.
  module Template (ψ : Γ → CofProp)
    (ψMatch : reindex' F (ats ∘ fst') ≡ reindex' X₀ fst)
    (φEquiv : ∀ x → (u : [ φ x ]) → Equiv (F .fst ((x , u) , s x)) (X₀ .fst x))
    (equivMatch : ∀ x → (u : [ φ x ]) (v : [ ψ x ]) →
      subst (Equiv ◆ X₀ .fst x) (cong (λ Bβ → Bβ .fst (x , u , v)) ψMatch) (φEquiv x u)
      ≡ idEquiv (reindex' X₀ (λ _ → x) .snd))
    where

    module F = UnionFib φ ψ (reindex' F ats) (reindex' X₀ fst) ψMatch
    open F public

    equiv : Π (Equiv' (fib .fst) (X₀ .fst ∘ fst))
    equiv = uncurry λ x →
      ∨-elim (φ x) (ψ x) _
        (λ u →
          subst (Equiv ◆ X₀ .fst x)
            (cong (λ Bβ → Bβ .fst (x , u)) (symm left))
            (φEquiv x u))
        (λ v →
          subst (Equiv ◆ X₀ .fst x)
            (cong (λ Bβ → Bβ .fst (x , v)) (symm right))
            (idEquiv (reindex' X₀ (λ _ → x) .snd)))
        (λ u v →
          trans
            (trans
              (adjustSubstEq (Equiv ◆ X₀ .fst x)
                (cong (λ Bβ → Bβ .fst (x , u , v)) ψMatch)
                refl
                (trans
                  (cong (curry (fib .fst) x) (trunc _ _))
                  (cong (λ Bβ → Bβ .fst (x , u)) (symm left)))
                (cong (λ Bβ → Bβ .fst (x , v)) (symm right))
                (equivMatch x u v))
              (symm
                (substTrans (Equiv ◆ X₀ .fst x)
                  (cong (curry (fib .fst) x) (trunc _ _))
                  (cong (λ Bβ → Bβ .fst (x , u)) (symm left)))))
            (substCongAssoc (Equiv ◆ X₀ .fst x)
              (curry (fib .fst) x)
              (trunc _ _)
              _))

  rsMatch : reindex' F (ats ∘ fst') ≡ reindex' X₀ fst
  rsMatch =
    (trans
      (cong (reindex' ◆ fst') match)
      (cong (reindex' F) (funext λ {(x , u , eq) → Σext refl (symm eq)})))

  rsEquiv : ∀ x → (u : [ φ x ]) → Equiv (F .fst ((x , u) , s x)) (X₀ .fst x)
  rsEquiv x u =
    subst (Equiv (F .fst ((x , u) , s x)))
      (cong (λ Bβ → Bβ .fst (x , u)) match)
      (coerceEquiv S (reindex' F (λ i → ((x , u) , i)) .snd) (s x) (r x))

  rsEquivMatch : (x : Γ) (u : [ φ x ]) (eq : r x ≡ s x) →
    subst (Equiv ◆ X₀ .fst x) (cong (λ Bβ → Bβ .fst (x , u , eq)) rsMatch) (rsEquiv x u)
    ≡ idEquiv (reindex' X₀ (λ _ → x) .snd)
  rsEquivMatch x u eq =
    lemma
      (reindex' F (λ _ → (x , u) , r x) .snd)
      (reindex' X₀ (λ _ → x) .snd)
      (cong (λ Bβ → Bβ .fst (x , u , eq)) rsMatch)
      (cong (λ t → F .fst ((x , u) , t)) (symm eq))
      (cong (λ Bβ → Bβ .fst (x , u)) match)
      (Σeq₂
        (cong (λ Bβ → (Bβ .fst (x , u) , reindex' Bβ (λ _ → (x , u)) .snd)) match)
        (cong (λ Bβ → Bβ .fst (x , u)) match))
      (coerceEquiv S (reindex' F (λ i → ((x , u) , i)) .snd) (s x) (r x))
      (trans
        (coerceEquivCap S (reindex' F (λ i → ((x , u) , i)) .snd) (r x))
        (trans
          (congdep
            (λ t → coerceEquiv S (reindex' F (λ i → (x , u) , i) .snd) t (r x))
            (symm eq))
          (symm
            (substCongAssoc
              (Equiv ◆ fst (reindex' F (λ _ → (x , u) , r x)) tt)
              (λ t → F .fst ((x , u) , t))
              (symm eq)
              (coerceEquiv S (reindex' F (λ i → (x , u) , i) .snd) (s x) (r x))))))
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
  (F : Fib ℓ' (res Γ φ × ⟨ S ⟩))
  (X₀ : Fib ℓ' Γ) (match : reindex' F (λ {(x , u) → (x , u) , r x}) ≡ reindex' X₀ fst)
  where

  module _ (s : Γ → ⟨ S ⟩) where

    open Box S r φ F X₀ match s

    LargeComp : Fib ℓ' Γ
    LargeComp = SGlueFib (λ x → φ x ∨ S ∋ r x ≈ s x) fib X₀ equiv

    -- EC: slow
    LargeCompMatch : reindex' F ats ≡ reindex' LargeComp fst
    LargeCompMatch =
      trans
        (cong
          (reindex' ◆ inl' φ (λ x → S ∋ r x ≈ s x))
          (SGlueFibStrictness (λ x → φ x ∨ S ∋ r x ≈ s x) fib X₀ equiv))

        (symm left)

  -- EC: slow
  LargeCap : LargeComp r ≡ X₀
  LargeCap =
    trans
      (cong (reindex' ◆ f₀) right)
      (cong (reindex' ◆ (inr' φ (λ x → S ∋ r x ≈ r x) ∘ f₀))
        (symm (SGlueFibStrictness (λ x → φ x ∨ S ∋ r x ≈ r x) fib X₀ equiv)))
    where
    open Box S r φ F X₀ match r

    f₀ : Γ → res Γ (λ x → S ∋ r x ≈ r x)
    f₀ x = x , refl

module _ {ℓ ℓ'} {Γ : Set ℓ}
  (S T : Shape) (σ : ShapeHom S T) (r : Γ → ⟨ S ⟩)
  (φ : Γ → CofProp)
  (F : Fib ℓ' (res Γ φ × ⟨ T ⟩))
  (X₀ : Fib ℓ' Γ) (match : reindex' F (λ {(x , u) → (x , u) , ⟪ σ ⟫ (r x)}) ≡ reindex' X₀ fst)
  (s : Γ → ⟨ S ⟩)
  where

  module S = Box S r φ (reindex' F (id× ⟪ σ ⟫)) X₀ match s
  module T = Box T (⟪ σ ⟫ ∘ r) φ F X₀ match (⟪ σ ⟫ ∘ s)

  varyEquiv : T.rsEquiv ≡ S.rsEquiv
  varyEquiv = funext λ x → funext λ u →
    cong
      (subst (Equiv (F .fst ((x , u) , ⟪ σ ⟫ (s x)))) (cong (λ Bβ → Bβ .fst (x , u)) match))
      (varyCoerceEquiv S T σ (reindex' F (λ i → (x , u) , i) .snd) (s x) (r x))

  -- EC: slow
  LargeVary
    : LargeComp T (⟪ σ ⟫ ∘ r) φ F X₀ match (⟪ σ ⟫ ∘ s)
      ≡ LargeComp S r φ (reindex' F (id× ⟪ σ ⟫)) X₀ match s
  LargeVary =
    cong
      (λ {(((ψ , ψMatch) , φEquiv) , equivMatch) →
        SGlueFib (λ x → φ x ∨ ψ x)
          (S.Template.fib ψ ψMatch φEquiv equivMatch)
          X₀
          (S.Template.equiv ψ ψMatch φEquiv equivMatch)})
      (Σext
        (×ext
          (Σext (funext λ x → ≈Equivariant σ (r x) (s x)) uipImp)
          varyEquiv)
        (funext λ x → funext λ u → funext λ v → uipImp))

-- EC: TODO stability of FEP under substitution in the context Γ
