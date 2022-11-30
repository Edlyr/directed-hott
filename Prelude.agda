{-# OPTIONS --rewriting #-}

module Prelude where

open import Agda.Primitive public
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )


-- We cannot use Martin-Löf's general equality for rewriting, so use use a separate rewriting postulate instead of Agda.Builtin.Equality.Rewrite
postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set a
{-# BUILTIN REWRITE _↦_ #-}

variable
  ℓ ℓ' : Level

---
-- Axioms and computations rules for Randall North's Directed Type theory
-- https://arxiv.org/abs/1807.10566
-- I use the axioms described on page 17 of Paige North's slides
-- rather than the more complicated ones in her paper.
-- https://paigenorth.github.io/talks/penn.pdf
---

postulate
  _core : Type ℓ → Type ℓ
  _op : Type ℓ → Type ℓ

  i : {T : Type ℓ} → T core → T
  i-op : {T : Type ℓ} → T core → T op

  hom : {T : Type ℓ} → T op → T → Type ℓ
  id : {T : Type ℓ} (t : T core) → hom (i-op t) (i t)

  eR : -- Right elimination rule
    {T : Type ℓ}
    (D : (s : T core) (t : T) → hom (i-op s) t → Type ℓ')
    (d : (s : T core) → D s (i s) (id s))
    (s' : T core)
    (t' : T)
    (f' : hom (i-op s') t') →
    D s' t' f'

  eL : -- Left elimination rule
    {T : Type ℓ}
    (D : (s : T op) (t : T core) → hom s (i t) → Type ℓ')
    (d : (s : T core) → D (i-op s) s (id s))
    (s' : T op)
    (t' : T core)
    (f' : hom s' (i t')) →
    D s' t' f'

  eR-eq : -- Right computation rule
    {T : Type ℓ}
    (D : (s : T core) (t : T) → hom (i-op s) t → Type ℓ')
    (d : (s : T core) → D s (i s) (id s))
    (s' : T core) →
    eR D d s' (i s') (id s') ↦ d s'

  eL-eq : -- Left computation rule
    {T : Type ℓ}
    (D : (s : T op) (t : T core) → hom s (i t) → Type ℓ')
    (d : (s : T core) → D (i-op s) s (id s))
    (s' : T core) →
    eL D d (i-op s') s' (id s') ↦ d s'

{-# REWRITE eR-eq eL-eq #-} -- We ask eR-eq and eL-eq to hold judgmentally

transportR :
  {T : Type ℓ}
  (B : T → Type ℓ')
  (s : T core)
  (t : T) →
  hom (i-op s) t →
  B (i s) → B t
transportR B = eR (λ s t _ → B (i s) → B t) (λ s x → x)

transportL :
  {T : Type ℓ}
  (B : T op → Type ℓ')
  (s : T op)
  (t : T core) →
  hom s (i t) →
  B s → B (i-op t)
transportL B = eL (λ s t _ → B s → B (i-op t)) (λ t x → x)



-- What we want :
--   hom→map : (A : Type op) (B : Type) → hom A B → (A → B)
-- However, agda's "→"-types cannot be changed to respect the variance of the arguments
-- So we have to settle with weaker, less functorial versions.
-- Also, it's not clear that the above could be built in complete generality using only the current axioms.

hom→map : {A : Type ℓ core} {B : Type ℓ} → hom (i-op A) B → (i A) → B
hom→map {A = A} {B} = transportR (λ X → X) A B

-- Should something like this work ?
-- Here there is no way to construct an element in the core of (i X → i X).
-- usual constructions from type theory should work inside the core of types. Lambda-abstraction ?
--   hom→map-core : {A : Type ℓ core} {B : Type ℓ} → hom (i-op A) B → ((i A) → B) core
--   hom→map-core {A = A} {B} = eR (λ A B _ → (i A → B) core) (λ X → {!!}) A B



-- Definition of Martin Löf's equality restricted to cores.
postulate
  _≡_ : {A : Type ℓ} → A core → A core → Type ℓ
  refl : {A : Type ℓ} {a : A core} → a ≡ a
  J : {A : Type ℓ} {a : A core}
    → (B : (a' : A core) → a ≡ a' → Type ℓ')
    → (B a refl)
    → (a' : A core) (p : a ≡ a') → B a' p
  J-eq : {A : Type ℓ} {a : A core}
    → (B : (a' : A core) → a ≡ a' → Type ℓ')
    → (ind : B a refl)
    → J B ind a refl ↦ ind
  {-# REWRITE J-eq #-}
  
-- We would like to state something like "hom→map id ≡ (λ x → x)",
-- but "hom→map id" is an element of (X → X). In order to state some
-- equality, it would need to be in "(X → X) core".
-- This would require a definition of hom→map-core as above,
-- which sadly cannot be done in the current Type Theory.
