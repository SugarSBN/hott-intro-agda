{-# OPTIONS --without-K --exact-split --safe #-}

module 06-universes where

import 05-identity
open 05-identity public

-- Section 6.3 Observational equality on the natural numbers

-- Definition 6.3.1

Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = 𝟙
Eq-ℕ zero-ℕ (succ-ℕ n) = 𝟘
Eq-ℕ (succ-ℕ n) zero-ℕ = 𝟘
Eq-ℕ (succ-ℕ n) (succ-ℕ m) = Eq-ℕ n m

-- Lemma 6.3.2
refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

-- Proposition 6.3.3
Eq-ℕ-eq : {x y : ℕ} → 
          x ≡ y → 
          Eq-ℕ x y
Eq-ℕ-eq {x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : {x y : ℕ} → 
          Eq-ℕ x y → 
          x ≡ y
eq-Eq-ℕ {zero-ℕ} {zero-ℕ} e = refl
eq-Eq-ℕ {succ-ℕ n} {succ-ℕ m} e = ap succ-ℕ (eq-Eq-ℕ {n} {m} e)

-- Section 6.4 Peano's seventh and eighth axioms

-- Theorem 6.4.1
is-injective-succ-ℕ : {x y : ℕ} → 
                      (succ-ℕ x) ≡ (succ-ℕ y) → 
                      x ≡ y
is-injective-succ-ℕ e = eq-Eq-ℕ (Eq-ℕ-eq e)

peano-7 : {x y : ℕ} → 
          (x ≡ y → (succ-ℕ x) ≡ (succ-ℕ y)) × ((succ-ℕ x) ≡ (succ-ℕ y) → x ≡ y)
peano-7 = pair (ap succ-ℕ) is-injective-succ-ℕ

peano-8 : {n : ℕ} →
          ¬ (zero-ℕ ≡ (succ-ℕ n))
peano-8 {n} e = Eq-ℕ-eq e