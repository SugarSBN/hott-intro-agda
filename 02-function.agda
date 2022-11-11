{-# OPTIONS --without-K --exact-split --safe #-}

module 02-function where

import 00-preamble
open 00-preamble public

_∘_ : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → 
      (g : B → C) → 
      (f : A → B) → 
      (A → C)
g ∘ f = λ a → g (f a)