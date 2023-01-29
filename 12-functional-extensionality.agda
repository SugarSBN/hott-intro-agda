{-# OPTIONS --without-K --exact-split #-}

module 12-functional-extensionality where

import 11-higher-truncate
open 11-higher-truncate public

htpy-eq : {i j : Level} {A : UU i} {B : A → UU j} → 
            (f g : (x : A) → B x) → 
                (f ≡ g) → (f ~ g)
htpy-eq f g refl x = refl

postulate FUNEXT : {i j : Level} {A : UU i} {B : A → UU j} → 
                    (f g : (x : A) → B x) → 
                        (f ≡ g) ↔ (f ~ g)

-- Theorem 11.3.1
currying : {i j k : Level} {A : UU i} {B : A → UU j} {X : UU k} → 
            (Σ A B → X) ≃ ((x : A) → (B x) → X)
currying {A = A} {B = B} {X = X} = pair f (pair f-section f-retraction)
    where
        f : (Σ A B → X) → ((x : A) → (B x) → X)
        f = λ h x y → h (pair x y)

        g : ((x : A) → (B x) → X) → (Σ A B → X)
        g = λ h p → h (pr1 p) (pr2 p)
        
        f-section : section f 
        f-section = pair g eq' 
            where
                eq' : (f ∘ g) ~ id
                eq' x = refl
        pair-refl : (x : Σ A B) → x ≡ pair (pr1 x) (pr2 x)
        pair-refl (pair x y) = refl

        f-retraction : retraction f 
        f-retraction = pair g eq2
            where
                eq1 : (h : Σ A B → X) → (g ∘ f) h ~ h
                eq1 h p = ap h (inv (pair-refl p))

                eq2 : (g ∘ f) ~ id
                eq2 h = (pr2 (FUNEXT ((g ∘ f) h) h)) (eq1 h)

currying' : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} → 
            (A × B → X) ≃ (A → B → X)
currying' = currying

-- Type theoretical Yoneda lemma: families of maps out of the identity type are uniquely determined by their action on the reflexivity
--                                identification.
yoneda : {i j : Level} {A : UU i} {B : A → UU j} → 
            (a : A) → 
            ((x : A) → (a ≡ x) → B x) ≃ (B a)
yoneda {j = j} {A = A} {B = B} a = pair f (pair (pair g f-section) (pair g f-retraction))
    where
        f : ((x : A) → (a ≡ x) → B x) → (B a)
        f = λ h → h a refl

        g : (B a) → ((x : A) → (a ≡ x) → B x)
        g init x = ind {x} 
            where 
                P : {x : A} → (a ≡ x) → UU j 
                P {x} p = B x

                p0 : P {a} refl 
                p0 = init 

                ind : {x : A} → (p : a ≡ x) → P p
                ind = ind-≡ P p0

        f-section : (f ∘ g) ~ id 
        f-section x = refl

        eq0 : (x : A) → (h : (x : A) → (a ≡ x) → B x) → (((g ∘ f) h) x) ~ (h x)
        eq0 x h refl = refl

        eq0' : (x : A) → (h : (x : A) → (a ≡ x) → B x) → (((g ∘ f) h) x) ≡ (h x)
        eq0' x h = (pr2 (FUNEXT (((g ∘ f) h) x) (h x))) (eq0 x h)

        eq1 : (h : (x : A) → (a ≡ x) → B x) → (g ∘ f) h ~ h
        eq1 h x = eq0' x h

        eq1' : (h : (x : A) → (a ≡ x) → B x) → (g ∘ f) h ≡ h
        eq1' h = (pr2 (FUNEXT ((g ∘ f) h) h)) (eq1 h)

        f-retraction : (g ∘ f) ~ id
        f-retraction h = eq1' h
