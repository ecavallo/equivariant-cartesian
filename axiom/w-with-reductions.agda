{-

Axiomatization of (indexed) W-types with reductions.

-}
module axiom.w-with-reductions where

open import prelude
open import axioms

private variable
  ℓ ℓ' : Level

record Poly (ℓ : Level) : Type (lsuc ℓ) where
  field
    Constr : Type ℓ
    Arity : Constr → Type ℓ
    Red : Constr → Cof
    ev : (c : Constr) → [ Red c ] → Arity c

module _ (P : Poly ℓ) where
  open Poly P

  postulate
    W : Type ℓ

    sup : (c : Constr) (α : Arity c → W) → W
    red : (c : Constr) (α : Arity c → W) (x : [ Red c ]) → sup c α ≡ α (ev c x)

    W-elim : (X : W → Type ℓ')
      (s : (c : Constr) (α : Arity c → W) → ((a : Arity c) → X (α a)) → X (sup c α))
      (r : (c : Constr) (α : Arity c → W) (u : (a : Arity c) → X (α a))
           (x : [ Red c ]) → subst X (red c α x) (s c α u) ≡ u (ev c x))
      (w : W) → X w

    W-elim-β : (X : W → Type ℓ')
      (s : (c : Constr) (α : Arity c → W) → ((a : Arity c) → X (α a)) → X (sup c α))
      (r : (c : Constr) (α : Arity c → W) (u : (a : Arity c) → X (α a))
           (x : [ Red c ]) → subst X (red c α x) (s c α u) ≡ u (ev c x))
      (c : Constr)
      (α : Arity c → W)
      → W-elim X s r (sup c α) ≡ s c α (λ a → W-elim X s r (α a))

    {-# REWRITE W-elim-β #-}

record IxPoly (I : Type) (ℓ : Level) : Type (lsuc ℓ) where
  field
    Constr : I → Type ℓ
    Arity : {i : I} → Constr i → I → Type ℓ
    Red : {i : I} → Constr i → Cof
    ev : {i : I} (c : Constr i) → [ Red c ] → Arity c i

module _ {I : Type} (P : IxPoly I ℓ) where
  open IxPoly P

  postulate
    IxW : I → Type ℓ

    ixsup : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxW j) → IxW i
    ixred : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxW j)
      (x : [ Red c ]) → ixsup c α ≡ α i (ev c x)

    IxW-elim : (X : (i : I) → IxW i → Type ℓ')
      (s : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxW j)
           → ((j : I) (a : Arity c j) → X j (α j a)) → X i (ixsup c α))
      (r : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxW j)
           (u : (j : I) (a : Arity c j) → X j (α j a))
           (x : [ Red c ]) → subst (X i) (ixred c α x) (s c α u) ≡ u i (ev c x))
      (i : I) (w : IxW i) → X i w

    IxW-elim-β : (X : (i : I) → IxW i → Type ℓ')
      (s : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxW j)
           → ((j : I) (a : Arity c j) → X j (α j a)) → X i (ixsup c α))
      (r : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxW j)
           (u : (j : I) (a : Arity c j) → X j (α j a))
           (x : [ Red c ]) → subst (X i) (ixred c α x) (s c α u) ≡ u i (ev c x))
      (i : I)
      (c : Constr i)
      (α : (j : I) → Arity c j → IxW j)
      → IxW-elim X s r i (ixsup c α) ≡ s c α (λ j a → IxW-elim X s r j (α j a))

    {-# REWRITE IxW-elim-β #-}
