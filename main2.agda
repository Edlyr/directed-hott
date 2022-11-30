{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Level
Type : (ℓ : Level) → Set (suc ℓ)
Type ℓ = Set ℓ

private
  variable
    ℓ ℓ' : Level

sym : {T : Type ℓ} {s t : T} → s ≡ t → t ≡ s
sym refl = refl

symInvo : {T : Type ℓ} {s t : T} (p : s ≡ t) → sym (sym p) ≡ p
symInvo refl = refl

cong : {T : Type ℓ} {T' : Type ℓ'} (f : T → T') {s t : T} → s ≡ t → f s ≡ f t
cong f refl = refl

infixr 20 _∙_
_∙_ : {T : Type ℓ} {s t u : T} → s ≡ t → t ≡ u → s ≡ u
refl ∙ p = p

-- Axioms of Directed Type Theory
-- I use the axioms described on page 17 of Paige North's slides :
-- https://paigenorth.github.io/talks/penn.pdf

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
    eR D d s' (i s') (id s') ≡ d s'

  eL-eq : -- Left computation rule
    {T : Type ℓ}
    (D : (s : T op) (t : T core) → hom s (i t) → Type ℓ')
    (d : (s : T core) → D (i-op s) s (id s))
    (s' : T core) →
    eL D d (i-op s') s' (id s') ≡ d s'

{-# REWRITE eR-eq eL-eq #-} -- We ask eR-eq and eL-eq to hold judgmentally

-- Here I define right and left transport. In the end I didn't use them in what follows.
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

-- For any s : T core and t : T, isomorphism between
-- (i s ≡ t) and (hom (i-op s) t)

eq-to-homR : {T : Type ℓ} {s : T core} {t : T} → i s ≡ t → hom (i-op s) t
eq-to-homR refl = id _

hom-to-eqR : {T : Type ℓ} {s : T core} {t : T} → hom (i-op s) t → i s ≡ t
hom-to-eqR = eR (λ s t _ → i s ≡ t) (λ _ → refl) _ _

retractR : {T : Type ℓ} {s : T core} {t : T} (p : i s ≡ t) →
  hom-to-eqR (eq-to-homR p) ≡ p
retractR refl = refl

sectionR : {T : Type ℓ} {s : T core} {t : T} (f : hom (i-op s) t) →
  eq-to-homR (hom-to-eqR f) ≡ f
sectionR = eR (λ _ _ f → eq-to-homR (hom-to-eqR f) ≡ f) (λ _ → refl) _ _

-- Inversion of directed paths

inversion : {T : Type ℓ} {s t : T core} →
  hom (i-op s) (i t) → hom (i-op t) (i s)
inversion f = eq-to-homR (sym (hom-to-eqR f))

inv-involution : {T : Type ℓ} {s t : T core} (f : hom (i-op s) (i t)) →
  inversion (inversion f) ≡ f
inv-involution f = lemma1 ∙ lemma2 ∙ sectionR f where
  -- Unfolding :
  -- inversion t s (inversion s t f) =
  -- eq-to-homR (sym (hom-to-eqR (eq-to-homR (sym (hom-to-eqR f)))))

  lemma1 :
    eq-to-homR (sym (hom-to-eqR (eq-to-homR (sym (hom-to-eqR f))))) ≡
    eq-to-homR (sym (                        sym (hom-to-eqR f)))
  lemma1 = cong
    (λ x → eq-to-homR (sym x))
    (retractR (sym (hom-to-eqR f)))

  lemma2 : eq-to-homR (sym (sym (hom-to-eqR f))) ≡
           eq-to-homR (          hom-to-eqR f)
  lemma2 = cong eq-to-homR (symInvo (hom-to-eqR f))
  
