{-# OPTIONS --without-K --exact-split --safe #-}
module 03-naturals where

import 02-function
open 02-function public

data ℕ : UU lzero where
    zero-ℕ : ℕ
    succ-ℕ : ℕ → ℕ

ind-ℕ : {i : Level} (P : ℕ → UU i) → P zero-ℕ → ((n : ℕ) → P n → P (succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ P p0 ind zero-ℕ = p0
ind-ℕ P p0 ind (succ-ℕ n) = ind n (ind-ℕ P p0 ind n) 

add-ℕ : ℕ → ℕ → ℕ
add-ℕ n zero-ℕ = n 
add-ℕ n (succ-ℕ m) = succ-ℕ (add-ℕ n m)

mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ n zero-ℕ = zero-ℕ
mul-ℕ n (succ-ℕ m) = add-ℕ n (mul-ℕ n m)

sub-ℕ : ℕ → ℕ → ℕ 
sub-ℕ n zero-ℕ = n 
sub-ℕ zero-ℕ (succ-ℕ m) = zero-ℕ
sub-ℕ (succ-ℕ n) (succ-ℕ m) = sub-ℕ n m