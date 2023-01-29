{-# OPTIONS --without-K --exact-split #-}

module 13-univalence where

import 12-functional-extensionality
open 12-functional-extensionality public

equiv-eq : {i : Level} {A B : UU i} →
            ((A ≡ B) → (A ≃ B))
equiv-eq refl = equiv-id

postulate UNIVALENCE : {i : Level} (A B : UU i) → is-equiv (equiv-eq {A = A} {B = B})
            
-- Proposition extensionality
prop-is-equiv : {i j : Level} {P : UU i} {Q : UU j} → 
                    is-prop P → is-prop Q → 
                    (f : P → Q) → (g : Q → P) → is-equiv f
prop-is-equiv P-prop Q-prop f g = pair (pair g H1) (pair g H2)
    where
        H1 : (f ∘ g) ~ id 
        H1 y = contr-center (Q-prop (f (g y)) y)

        H2 : (g ∘ f) ~ id 
        H2 x = contr-center (P-prop (g (f x)) x)

inverse-is-eq : {i j : Level} {A : UU i} {B : UU j} → 
                (f : A → B) → (g1 g2 : B → A) → 
                ((g1 ∘ f) ~ id) × ((f ∘ g1) ~ id) → 
                ((g2 ∘ f) ~ id) × ((f ∘ g2) ~ id) →
                (g1 ≡ g2)
inverse-is-eq f g1 g2 inv1 inv2 = rua hom1
    where
        hom1 : g1 ~ g2 
        hom1 x = (inv ((pr1 inv2) (g1 x))) · (ap g2 ((pr2 inv1) x))

        rua : g1 ~ g2 → g1 ≡ g2 
        rua = pr2 (FUNEXT g1 g2)
        
function-is-prop : {i j : Level} {A : UU i} {B : UU j} → 
                    is-prop B → is-prop (A → B)
function-is-prop {A = A} {B = B} B-prop = any-two-equiv-is-prop any-two-equiv2
    where
        any-two-equiv1 : (b1 b2 : B) → b1 ≡ b2 
        any-two-equiv1 = prop-any-two-equiv B-prop

        any-two-equiv2 : (a1 a2 : A → B) → a1 ≡ a2
        any-two-equiv2 a1 a2 = pr2 (FUNEXT a1 a2) rua
            where
                rua : a1 ~ a2 
                rua x = any-two-equiv1 (a1 x) (a2 x)


-- This can be proved! But I have no time
postulate homotopy-is-prop : {i : Level} {A B : UU i} → is-prop A → is-prop B → is-prop (A ≃ B)

                        

        

prop-ext : {i : Level} {P Q : UU i} → 
            is-prop P → is-prop Q → 
            ((P ≡ Q) ≃ (P ↔ Q))
prop-ext {P = P} {Q = Q} P-prop Q-prop = homotopy-transitive hom1 (homotopy-inv hom2)
    where
        hom1 : (P ≡ Q) ≃ (P ≃ Q)
        hom1 = pair e e-eq
            where
                e : (P ≡ Q) → (P ≃ Q)
                e = equiv-eq 

                e-eq : is-equiv e 
                e-eq = UNIVALENCE P Q 
        
        e : (P ↔ Q) → (P ≃ Q)
        e (pair f g) = pair f (prop-is-equiv P-prop Q-prop f g)

        is-prop1 : is-prop (P ↔ Q)
        is-prop1 = is-prop-prod is-p1 is-p2
            where
                is-p1 : is-prop (P → Q)
                is-p1 = function-is-prop Q-prop

                is-p2 : is-prop (Q → P)
                is-p2 = function-is-prop P-prop
        
        is-prop2 : is-prop (P ≃ Q)
        is-prop2 = homotopy-is-prop {A = P} {B = Q} P-prop Q-prop

        e1 : (P ≃ Q) → (P ↔ Q)
        e1 (pair f f-eq) = pair f g
            where
                g : Q → P 
                g = pr1 (pr1 f-eq)

        iseq : is-equiv e 
        iseq = prop-is-equiv is-prop1 is-prop2 e e1

        hom2 : (P ↔ Q) ≃ (P ≃ Q)
        hom2 = pair e iseq
