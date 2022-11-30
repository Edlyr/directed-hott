{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Level
Type : (ℓ : Level) → Set (suc ℓ)
Type ℓ = Set ℓ

private
  variable
    ℓ ℓ' ℓ'' : Level

postulate
  _core : Type ℓ → Type ℓ
  _op : Type ℓ → Type ℓ

  i : {T : Type ℓ} → T core → T
  i-op : {T : Type ℓ} → T core → T op

  hom : {T : Type ℓ} → T op → T → Type ℓ
  id : {T : Type ℓ} → (t : T core) → hom (i-op t) (i t)

  eR :
    (T : Type ℓ)
    (Θ : T core → Type ℓ')
    (D : (s : T core) (t : T) (f : hom (i-op s) t) (θ : Θ s) → Type ℓ'')
    (d : (s : T core) (θ : Θ s) → D s (i s) (id s) θ)
    (s' : T core)
    (t' : T)
    (f' : hom (i-op s') t')
    (θ' : Θ s') →
    D s' t' f' θ'

  eL :
    (T : Type ℓ)
    (Θ : T core → Type ℓ')
    (D : (s : T op) (t : T core) (f : hom s (i t)) (θ : Θ t) → Type ℓ'')
    (d : (t : T core) (θ : Θ t) → D (i-op t) t (id t) θ)
    (s' : T op)
    (t' : T core)
    (f' : hom s' (i t'))
    (θ' : Θ t') →
    D s' t' f' θ'

  eR-eq :
    (T : Type ℓ)
    (Θ : T core → Type ℓ')
    (D : (s : T core) (t : T) (f : hom (i-op s) t) (θ : Θ s) → Type ℓ'')
    (d : (s : T core) (θ : Θ s) → D s (i s) (id s) θ)
    (s' : T core)
    (θ' : Θ s') →
    eR T Θ D d s' (i s') (id s') θ' ≡ d s' θ'

  eL-eq :
    (T : Type ℓ)
    (Θ : T core → Type ℓ')
    (D : (s : T op) (t : T core) (f : hom s (i t)) (θ : Θ t) → Type ℓ'')
    (d : (t : T core) (θ : Θ t) → D (i-op t) t (id t) θ)
    (t' : T core)
    (θ' : Θ t') →
    eL T Θ D d (i-op t') t' (id t') θ' ≡ d t' θ'
    
{-# REWRITE eR-eq eL-eq #-}

data Unit : Set where
  tt : Unit

eR-simpl :
  (T : Type ℓ)
  (D : (s : T core) (t : T) (f : hom (i-op s) t) → Type ℓ'')
  (d : (s : T core) → D s (i s) (id s))
  (s' : T core)
  (t' : T)
  (f' : hom (i-op s') t') →
  D s' t' f'
eR-simpl T D d s' t' f' = eR T (λ _ → Unit) (λ s t f _ → D s t f) (λ s _ → d s) s' t' f' tt

transportR :
  (T : Type ℓ)
  (E : T → Type ℓ')
  (e' : (s : T core) → E (i s))
  (s' : T core)
  (t' : T)
  (f' : hom (i-op s') t') →
  E t'
transportR T E e' s' t' f' = eR
  T
  (λ s → E (i s))
  (λ s t f e → E t)
  (λ s e → e)
  s' t' f' (e' s')

transport :
  {T : Type ℓ}
  (E : T → Type ℓ')
  {s : T core}
  {t : T}
  (f : hom (i-op s) t) →
  E (i s) →
  E t
transport {T = T} E {s = s} {t = t} f x = eR T
  (λ s' → E (i s'))
  (λ s' t' f' x' → E t')
  (λ s' θ' → θ')
  s t f x
  
transport-bis :
  {T : Type ℓ}
  (E : T → Type ℓ')
  {s : T core}
  {t : T}
  (f : hom (i-op s) t) →
  E (i s) →
  E t
transport-bis {T = T} E {s = s} {t = t} f = eR-simpl T (λ s' t' f' → E (i s') → E t') (λ _ x → x) s t f

lemma-transport : 
  {T : Type ℓ}
  (E : T → Type ℓ')
  {s : T core}
  {t : T}
  (f : hom (i-op s) t) →
  transport E f ≡ transport-bis E f
lemma-transport {T = T} E {s = s} {t = t} f = eR-simpl T (λ s t f → transport E f ≡ transport-bis E f) (λ s' → refl) s t f

comp : {T : Type ℓ} (a b : T core) (c : T) → (hom (i-op a) (i b)) → (hom (i-op b) c) → hom (i-op a) c
comp {T = T} a b c f g = transport (λ x → hom (i-op a) x) g f

eR-bis :
  (T : Type ℓ)
  (Θ : T core → Type ℓ')
  (D : (s : T core) (t : T) (f : hom (i-op s) t) (θ : Θ s) → Type ℓ')
  (d : (s : T core) (θ : Θ s) → D s (i s) (id s) θ)
  (s' : T core)
  (t' : T)
  (f' : hom (i-op s') t')
  (θ' : Θ s') →
  D s' t' f' θ'
eR-bis T Θ D d s' t' f' = eR-simpl T (λ s t f → (θ : Θ s) → D s t f θ) (λ s θ → d s θ) s' t' f'

sym : {T : Type ℓ} {x y : T} → x ≡ y → y ≡ x
sym refl = refl

----------------------------

test1 : (X : (Type ℓ) core) (Y : Type ℓ) → hom (i-op X) Y → (i X → Y)
test1 {ℓ = ℓ} X Y f = eR-simpl (Type ℓ) (λ X Y f → i X → Y) (λ s x → x) X Y f

test2 : (X : (Type ℓ) core) (Y : Type ℓ) → hom (i-op X) Y → (i X → Y)
test2 {ℓ = ℓ} X Y f = transport (λ X → X) f

----------------------------

test3 : (T : Type ℓ) (x y : T core) → hom (i-op x) (i y) → i x ≡ i y
test3 T x y f = transport (λ z → i x ≡ z) f refl

eq-to-hom : {T : Type ℓ} {x : T core} {y : T} → i x ≡ y → hom (i-op x) y
eq-to-hom refl = id _

sym-dir : (T : Type ℓ) (x y : T core) → hom (i-op x) (i y) → hom (i-op y) (i x)
sym-dir T x y f = eq-to-hom (sym (test3 T x y f))

hom-to-eq : (T : Type ℓ) (x : T core) (y : T) → hom (i-op x) y → i x ≡ y
hom-to-eq T x y f = transport (λ z → i x ≡ z) f refl

retract : (T : Type ℓ) (x : T core) (y : T) → (p : i x ≡ y) → hom-to-eq T x y (eq-to-hom p) ≡ p
retract T x _ refl = refl

section : (T : Type ℓ) (x : T core) (y : T) → (f : hom (i-op x) y) → eq-to-hom (hom-to-eq T x y f) ≡ f
section T x y f = eR-simpl T (λ x y f → eq-to-hom (hom-to-eq T x y f) ≡ f) (λ s → refl) x y f
