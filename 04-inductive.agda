{-# OPTIONS --without-K --exact-split --safe #-}
module 04-inductive where

import 00-preamble
open 00-preamble public

-- Definition 4.2.1
data unit : UU lzero where
    star : unit

𝟙 = unit

ind-unit : {i : Level} {P : 𝟙 → UU i} → P star → ((x : 𝟙) → P x)
ind-unit p star = p

-- Definition 4.3.1
data empty : UU lzero where

𝟘 = empty

ind-empty : {i : Level} {P : 𝟘 → UU i} → ((x : 𝟘) → P x)
ind-empty ()

ex-falso : {i : Level} {A : UU i} → 𝟘 → A
ex-falso = ind-empty

-- Definition 4.3.2
¬ : {i : Level} → UU i → UU i
¬ A = A → 𝟘

-- Proposition 4.3.3
functor-neg : {i1 i2 : Level} {P : UU i1} {Q : UU i2} → (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)

-- Definition 4.4.1
data bool : UU lzero where
    true  : bool
    false : bool

𝔹 = bool

-- Example 4.4.2
neg-bool : 𝔹 → 𝔹
neg-bool true = false
neg-bool false = true

conjunction : 𝔹 → 𝔹 → 𝔹
conjunction true true = true
conjunction true false = false
conjunction false true = false
conjunction false false = false

-- Definition 4.5.1
data coprod {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j) where
    inl : A → coprod A B
    inr : B → coprod A B

_∔_ = coprod

ind-coprod : {i j k : Level} {A : UU i} {B : UU j} (P : A ∔ B → UU k) → ((x : A) → P (inl x)) → ((y : B) → P (inr y)) → ((t : A ∔ B) → P t)
ind-coprod P f g (inl x) = f x
ind-coprod P f g (inr y) = g y

-- Remark 4.5.2
functor-coprod : {i1 i2 j1 j2 : Level} {A : UU i1} {B : UU i2} {A' : UU j1} {B' : UU j2} → (A → A') → (B → B') → ((A ∔ B) → (A' ∔ B'))
functor-coprod f g (inl x) = inl (f x)
functor-coprod f g (inr y) = inr (g y) 

-- Proposition 4.5.3
coprod-elim-left : {i j : Level} {A : UU i} {B : UU j} → ¬ B → A ∔ B → A
coprod-elim-left nb (inl x) = x
coprod-elim-left nb (inr y) = ex-falso (nb y)

coprod-elim-right : {i j : Level} {A : UU i} {B : UU j} → ¬ A → A ∔ B → B
coprod-elim-right na (inl x) = ex-falso (na x)
coprod-elim-right na (inr y) = y

-- Definition 4.6.1
data Σ {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
    pair : (x : A) → (B x → Σ A B)

_⋆_ = Σ

ind-Σ : {i j k : Level} {A : UU i} {B : A → UU j} → (P : A ⋆ B → UU k) → ((x : A) (y : B x) → P (pair x y)) → ((t : A ⋆ B) → P t)
ind-Σ P f (pair x y) = f x y

-- Remark 4.6.2
ev-pair : {i j k : Level} {A : UU i} {B : A → UU j} (P : A ⋆ B → UU k) → ((t : A ⋆ B) → P t) → ((x : A) (y : B x) → P (pair x y))
ev-pair P f x y = f (pair x y)         


-- Definition 4.6.3
pr1 : {i j : Level} {A : UU i} {B : A → UU j} → A ⋆ B → A
pr1 (pair a b) = a

pr2 : {i j : Level} {A : UU i} {B : A → UU j} → (t : A ⋆ B) → B (pr1 t) 
pr2 (pair a b) = b

-- Definition 4.6.4
prod : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
prod A B = A ⋆ (λ a → B)

_×_ = prod
