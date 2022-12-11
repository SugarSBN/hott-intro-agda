{-# OPTIONS --without-K --exact-split --safe #-}

module 07-finite-sets where

import 06-universes
open 06-universes public

{- Section 7.1 The congruence relations -}

{- Definition 7.1.1 -}

-- We introduce the divisibility relation. --

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → (mul-ℕ k m) ≡ n)

-- Example: div 3 6
_ : div-ℕ (succ-ℕ (succ-ℕ (succ-ℕ zero-ℕ))) (succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ zero-ℕ))))))
_ = pair (succ-ℕ (succ-ℕ zero-ℕ)) refl

div-add-ℕ : {d x y : ℕ} → 
            div-ℕ d x → 
            div-ℕ d y → 
            div-ℕ d (add-ℕ x y)
div-add-ℕ {d} {x} {y} (pair d1 refl) (pair d2 refl) = pair (add-ℕ d1 d2) (mul-right-distribution-ℕ {d1} {d2} {d})

{- Definition 7.1.3 -}

{- We define the congruence relation on ℕ and we do some bureaucracy that will
   help us in calculations involving the congruence relations. -}

dist-ℕ : ℕ → ℕ → ℕ
dist-ℕ zero-ℕ m = m 
dist-ℕ (succ-ℕ n) zero-ℕ = succ-ℕ n 
dist-ℕ (succ-ℕ n) (succ-ℕ m) = dist-ℕ n m 



self-dist-ℕ : {x : ℕ} → (dist-ℕ x x) ≡ zero-ℕ
self-dist-ℕ {zero-ℕ} = refl 
self-dist-ℕ {succ-ℕ x} = self-dist-ℕ {x}


symmetric-dist-ℕ : {x y : ℕ} → (dist-ℕ x y) ≡ (dist-ℕ y x)
symmetric-dist-ℕ {zero-ℕ} {zero-ℕ} = refl 
symmetric-dist-ℕ {succ-ℕ x} {zero-ℕ} = refl
symmetric-dist-ℕ {zero-ℕ} {succ-ℕ y} = refl
symmetric-dist-ℕ {succ-ℕ x} {succ-ℕ y} = symmetric-dist-ℕ {x} {y}

dist-add-ℕ : {x y : ℕ} → 
             (x <= y) → 
             (add-ℕ x (dist-ℕ x y)) ≡ y
dist-add-ℕ {zero-ℕ} {zero-ℕ} e = refl 
dist-add-ℕ {zero-ℕ} {succ-ℕ y} e = left-unit-law-add-ℕ (succ-ℕ y)
dist-add-ℕ {succ-ℕ x} {succ-ℕ y} e = (left-successor-law-add-ℕ x (dist-ℕ x y)) · (ap succ-ℕ (dist-add-ℕ {x} {y} e))


cong-ℕ : ℕ → ℕ → ℕ → UU lzero 
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

_≡_mod_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod k = cong-ℕ k x y

{- Proposition 7.1.4 -}

-- We show that cong-ℕ is an equivalence relation.

reflexive-cong-ℕ : {k x : ℕ} → x ≡ x mod k 
reflexive-cong-ℕ {k} {x} = pair zero-ℕ ((mul-zero-left-ℕ {k}) · (inv (self-dist-ℕ {x})))

symmetric-cong-ℕ : {k x y : ℕ} →
                   x ≡ y mod k → 
                   y ≡ x mod k 
symmetric-cong-ℕ {k} {x} {y} (pair d p) = pair d (p · (symmetric-dist-ℕ {x} {y}))

{-
transitive-cong-ℕ : {k x y z : ℕ} → 
                    x ≡ y mod k → 
                    y ≡ z mod k → 
                    x ≡ z mod k 
-}

