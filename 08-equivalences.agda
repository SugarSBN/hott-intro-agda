{-# OPTIONS --without-K --exact-split --safe #-}

module 08-equivalences where

import 07-finite-sets
open 07-finite-sets public

-- Section 8.1 Homotopies

-- Definition 8.1.2

_~_ : {i j : Level} {A : UU i} {B : A → UU j} → 
      (f g : (x : A) → B x) → 
      UU (i ⊔ j)
            
f ~ g = (x : _) → (f x) ≡ (g x) 

-- Example 
id : {i : Level} {A : UU i} → (x : A) → A
id x = x

neg-neg : (neg-bool ∘ neg-bool) ~ id 
neg-neg true = refl
neg-neg false = refl

-- Reflexivity of homotopy
refl-homotopy : {i j : Level} {A : UU i} {B : A → UU j} → 
                (f : (x : A) → B x) → f ~ f
refl-homotopy f x = refl

-- Inverse of homotopy
inv-homotopy : {i j : Level} {A : UU i} {B : A → UU j} → 
               {f g : (x : A) → B x} →
               f ~ g → g ~ f
inv-homotopy H x = inv (H x)

-- Composition of homotopies
_·h_ : {i j : Level} {A : UU i} {B : A → UU j} → 
       {f g h : (x : A) → B x} →
       f ~ g → g ~ h → f ~ h
(H ·h K) x = (H x) · (K x) 

-- Associativity of Composition of homotopies
assoc-homotopies : {i j : Level} {A : UU i} {B : A → UU j} → 
                   {f g h k : (x : A) → B x} →
                   (H : f ~ g) (K : g ~ h) (L : h ~ k) →
                   ((H ·h K) ·h L) ~ (H ·h (K ·h L))
assoc-homotopies H K L x = assoc (H x) (K x) (L x)

-- Unit law of homotopy
left-unit-homotopy : {i j : Level} {A : UU i} {B : A → UU j} → 
                     {f g : (x : A) → B x} → 
                     (H : f ~ g) → 
                     ((refl-homotopy f) ·h H) ~ H
left-unit-homotopy H x = refl

right-unit-homotopy : {i j : Level} {A : UU i} {B : A → UU j} → 
                      {f g : (x : A) → B x} → 
                      (H : f ~ g) →
                      (H ·h (refl-homotopy g)) ~ H
right-unit-homotopy H x = right-unit (H x)


-- Inverse law of homotopy
left-inv-homotopy : {i j : Level} {A : UU i} {B : A → UU j} → 
                    {f g : (x : A) → B x} →
                    (H : f ~ g) → 
                    ((inv-homotopy H) ·h H) ~ (refl-homotopy g)
left-inv-homotopy H x = left-inv (H x)

right-inv-homotopy : {i j : Level} {A : UU i} {B : A → UU j} → 
                     {f g : (x : A) → B x} →
                     (H : f ~ g) → 
                     (H ·h (inv-homotopy H)) ~ (refl-homotopy f)
right-inv-homotopy H x = right-inv (H x)


-- Definition of whisk
left-whisk-homotopy : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → 
                      (h : B → C) → 
                      {f g : A → B} →
                      (f ~ g) → ((h ∘ f) ~ (h ∘ g))
left-whisk-homotopy h H x = ap h (H x)
_·l_ = left-whisk-homotopy

right-whisk-homotopy : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → 
                       {f g : B → C} →
                       (f ~ g) → (h : A → B) → ((f ∘ h) ~ (g ∘ h))
right-whisk-homotopy H h x = H (h x)
_·r_ = right-whisk-homotopy


-- Definition of section and retraction
section : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
section {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)
-- 「section f」 is a proposition saying: 「f」 has a section.

retraction : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retraction {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)
-- 「retraction f」 is a proposition saying: 「f」 has a retraction.

-- Definition of equivalence (Bilatural map)
is-equiv : {i j : Level} {A : UU i} {B : UU j} → 
           (f : A → B) → 
           UU (i ⊔ j)
is-equiv f = section f × retraction f
-- 「is-equiv f」 is a proposition saying: 「f」 is an equivalence, meaning that it has both section and retraction
_≃_ : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)
-- 「A ≃ B」 is a proposition saying: 「A」 and 「B」 are equivalent, meaning that there is an equivalence between 「A」 and 「B」.

-- Example: A ≃ A, and id_A is an equivalence
is-equiv-id : {i : Level} {A : UU i} → 
              is-equiv (id {i} {A})
is-equiv-id = pair (pair id (λ x → refl)) (pair id (λ x → refl))

equiv-id : {i : Level} {A : UU i} → 
           A ≃ A
equiv-id = pair id is-equiv-id

-- Example: ℤ ≃ ℤ, and id_ℤ, succ-ℤ are equivalences.
pred-succ-ℤ : (pred-ℤ ∘ succ-ℤ) ~ id
pred-succ-ℤ (inr (inl star)) = refl
pred-succ-ℤ (inr (inr n)) = refl 
pred-succ-ℤ (inl zero-ℕ) = refl
pred-succ-ℤ (inl (succ-ℕ n)) = refl

succ-pred-ℤ : (succ-ℤ ∘ pred-ℤ) ~ id
succ-pred-ℤ (inr (inl star)) = refl
succ-pred-ℤ (inr (inr zero-ℕ)) = refl
succ-pred-ℤ (inr (inr (succ-ℕ n))) = refl
succ-pred-ℤ (inl n) = refl

is-equiv-succ-ℤ : is-equiv succ-ℤ
is-equiv-succ-ℤ = pair (pair pred-ℤ succ-pred-ℤ) (pair pred-ℤ pred-succ-ℤ)

is-equiv-pred-ℤ : is-equiv pred-ℤ
is-equiv-pred-ℤ = pair (pair succ-ℤ pred-succ-ℤ) (pair succ-ℤ succ-pred-ℤ)

equiv-ℤ : ℤ ≃ ℤ
equiv-ℤ = pair succ-ℤ is-equiv-succ-ℤ

-- Definition of inverse
has-inverse : {i j : Level} {A : UU i} {B : UU j} → 
              (f : A → B) → 
              UU (i ⊔ j)
has-inverse {i} {j} {A} {B} f = Σ (B → A) (λ g → ((g ∘ f) ~ id) × ((f ∘ g) ~ id))

-- Proposition: has inverse => is equivalence
has-inversion-is-equiv : {i j : Level} {A : UU i} {B : UU j} → 
                         (f : A → B) → 
                         has-inverse f → is-equiv f
has-inversion-is-equiv {i} {j} {A} {B} f (pair g (pair H K)) = pair (pair g K) (pair g H)

-- Definition of Σ-type equality
Σ-eq : {i j : Level} {A : UU i} {B : A → UU j} → 
       (s t : Σ A B) → UU (i ⊔ j)
Σ-eq {i} {j} {A} {B} s t = Σ ((pr1 s) ≡ (pr1 t)) (λ α → ((tr {B = B} α (pr2 s)) ≡ (pr2 t)))
-- pair (a : A) (b : B a) ≡ pair (c : A) (d : B c) <=>
-- a ≡ c ∧ (tr B (a ≡ c) b ≡ d) 
-- tr B (a ≡ c) : B a → B c

-- Proposition: Σ-type equality is reflexitive
Σ-eq-refl : {i j : Level} {A : UU i} {B : A → UU j} → 
            (s : Σ A B) → 
            Σ-eq s s
Σ-eq-refl (pair a b) = pair refl refl

pair-eq : {i j : Level} {A : UU i} {B : A → UU j} → 
          {s t : Σ A B} →
          (s ≡ t) → Σ-eq s t
pair-eq {s = s} refl = Σ-eq-refl s

-- Definition of product equality
prod-eq : {i j : Level} {A : UU i} {B : UU j} → 
          (s t : A × B) → UU (i ⊔ j)
prod-eq s t = (pr1 s ≡ pr1 t) × (pr2 s ≡ pr2 t)

eq-pair : {i j : Level} {A : UU i} {B : A → UU j} → 
          {s t : Σ A B} → 
          (α : pr1 s ≡ pr1 t) → (tr {B = B} α (pr2 s)) ≡ (pr2 t) → s ≡ t 
eq-pair {B = B} {pair x y} {pair x1 y1} refl refl = refl

Σ-eq-≡ : {i j : Level} {A : UU i} {B : A → UU j} → 
          {s t : Σ A B} →
           Σ-eq s t → s ≡ t
Σ-eq-≡ (pair α β) = eq-pair α β

logic-equiv : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
logic-equiv A B = (A → B) × (B → A)
_↔_ = logic-equiv