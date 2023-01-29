{-# OPTIONS --without-K --exact-split --safe #-}

module 11-higher-truncate where

import 10-fundamental-theorem
open 10-fundamental-theorem public

-- Definition of Proposition
is-prop : {i : Level} (A : UU i) → UU i 
is-prop A = (x : A) → (y : A) → is-contr (x ≡ y)




        

-- Universes of propositions
UU-prop : (i : Level) → UU (lsuc i)
UU-prop i = Σ (UU i) is-prop

homotopy-prop' : {i j : Level} {A : UU i} {B : UU j} → 
                (A ≃ B) → is-prop B → is-prop A
homotopy-prop' {A = A} {B = B} simeq B-is-prop x y = contr2
    where
        e : A → B 
        e = pr1 simeq 

        e-eq : is-equiv e 
        e-eq = pr2 simeq 

        ape : (x ≡ y) → (e x ≡ e y)
        ape p = ap e p

        ape-eq : is-equiv ape
        ape-eq = equiv-is-emb e e-eq x y

        hom : (x ≡ y) ≃ (e x ≡ e y)
        hom = pair ape ape-eq

        contr1 : is-contr(e x ≡ e y)
        contr1 = B-is-prop (e x) (e y)

        contr2 : is-contr (x ≡ y)
        contr2 = contr-homotopy (homotopy-inv hom) contr1


homotopy-prop : {i j : Level} {A : UU i} {B : UU j} → 
                (A ≃ B) → is-prop A ↔ is-prop B
homotopy-prop {A = A} {B = B} simeq = pair rua2 rua1
    where
        rua1 : is-prop B → is-prop A 
        rua1 h = homotopy-prop' simeq h 
        
        rua2 : is-prop A → is-prop B 
        rua2 h = homotopy-prop' (homotopy-inv simeq) h 

-- Example : Any contractible type is a proposition
contr-is-prop : {i : Level} {A : UU i} → 
                    is-contr A → is-prop A
contr-is-prop A-is-contr x y = pair center' eq'
    where
        center = contr-center A-is-contr     -- = a : A
        x-center = (pr2 A-is-contr) x        -- : a ≡ x 
        y-center = (pr2 A-is-contr) y        -- : a ≡ y
        center' =  (inv x-center) · y-center -- : x ≡ y
        eq' : (r : x ≡ y) → center' ≡ r      
        eq' refl = left-inv ((pr2 A-is-contr) x) -- when r = refl, x-center = y-center, so center' is (int p) · p 

-- Lemma 10.1.4
-- homo-types-are-prop : {i j : Level} {A : UU i} {B : UU j} → 
--                        (A ≃ B) → is-prop A → is-prop B 


-- Definition of sets
is-set : {i : Level} (A : UU i) → UU i 
is-set A = (x y : A) → is-prop(x ≡ y)

axiom-K : {i : Level} → UU i → UU i
axiom-K A = (x : A) (p : x ≡ x) → refl ≡ p 



-- Theorem 10.1.3 If for a type A, any two terms of A are equal, then A is a proposition
--                which means that proposition is proof irrevalent
any-two-equiv-is-prop : {i : Level} {A : UU i} → 
                         (is-prop' : (x y : A) → (x ≡ y)) → is-prop(A) 
any-two-equiv-is-prop {i = i} {A = A} H x y = pair center eq' 
    where
        c : (z : A) → x ≡ z
        c z = (inv (H x x)) · (H x z) 
        center = c y
        eq' : (r : x ≡ y) → c y ≡ r
        eq' = (ind-≡ P p) {y}
            where
                P : {z : A} → (x ≡ z) → UU i  -- Path induction : definition of proposition
                P {z} p = c z ≡ p

                p : P {x} refl                -- Here we need to construct c, so that
                                              -- c x ≡ refl
                p = left-inv (H x x)          -- Path induction : proof of initial value : P {x} refl

prop-any-two-equiv : {i : Level} {A : UU i} → 
                      is-prop(A) → (x y : A) → x ≡ y 
prop-any-two-equiv A-is-prop x y = center 
    where
        center = pr1 (A-is-prop x y)
        
-- Lemma 10.2.2 A type A is a set if and only if it satisfies axiom-K 
lemma10-2-2 : {i : Level} {A : UU i} → 
                is-set A → axiom-K A 
lemma10-2-2 A-is-set x p = center
    where
        is-p = A-is-set x x        -- : is-prop(x ≡ x) = (p1 : x ≡ x) → (p2 : x ≡ x) → is-contr(p1 ≡ p2)
        is-c = is-p refl p         -- : is-contr(refl ≡ p)
        center = contr-center is-c -- : refl ≡ p

lemma10-2-2' : {i : Level} {A : UU i} → 
                axiom-K A → is-set A
lemma10-2-2' A-axiom-K x y = any-two-equiv-is-prop tmp  -- to prove : is-prop(x ≡ y)
    where
        tmp : (p1 p2 : x ≡ y) → p1 ≡ p2
        tmp p1 p2 = inv t6
            where
                t1 = A-axiom-K x (p1 · (inv p2)) -- : refl ≡ p1 · (inv p2)
                t2 = ap (λ β → β · p2) t1      -- : refl · p2 ≡ (p1 · (inv p2)) · p2 
                t3 = assoc p1 (inv p2) p2    -- : (p1 · (inv p2)) · p2 ≡ p1 · ((inv p2) · p2)
                t4 = left-inv p2             -- : (inv p2) · p2 ≡ refl
                t5 = ap (λ β → p1 · β) t4    -- : p1 · ((inv p2) · p2) ≡ p1 · refl
                t6 = ((left-unit p2) · ((t2 · t3) · t5)) · (right-unit p1)          -- : p2 ≡ p1

set-equiv-axiom-K : {i : Level} {A : UU i} → 
                    is-set A ↔ axiom-K A
set-equiv-axiom-K = pair lemma10-2-2 lemma10-2-2'

-- Theorem 10.2.3 
Theorem10-2-3 : {i j : Level} {A : UU i} {R : A → A → UU j} → 
                (allp : (x y : A) → is-prop (R x y)) → 
                (ρ : (x : A) → R x x) → 
                (mp : (x y : A) → R x y → x ≡ y) → 
                (fam : (x y : A) → x ≡ y → R x y) → 
                (x y : A) → is-equiv (fam x y)
Theorem10-2-3 {j = j} {A = A} {R = R} allp ρ mp fam x y = fam-eq y
    where
        P : {y : A} → (x ≡ y) → UU j 
        P {y} p = R x y

        ptd : (y : A) → (x ≡ y) → R x y 
        ptd y = ind-≡ P (ρ x) {y}

        alleq : (x y : A) → (α β : R x y) → α ≡ β 
        alleq x y α β = pr1 contr
            where
                contr = allp x y α β

        totF : Σ A (λ y → R x y) → Σ A (λ y → x ≡ y)
        totF = tot (mp x)

        retract : retraction totF 
        retract = pair (tot ptd) H 
            where
                tmp : (α : A) → (y1 y2 : R x α) → Σ-eq (pair α y1) (pair α y2) 
                tmp α y1 y2 = pair refl (alleq x α y1 y2) 
                
                tmp1 : (α : A) → (y1 y2 : R x α) → (pair α y1) ≡ (pair α y2)
                tmp1 α y1 y2 = Σ-eq-≡ (tmp α y1 y2)
                
                totP : Σ A (λ y → x ≡ y) → Σ A (λ y → R x y)
                totP = tot ptd 
                
                H :  (totP ∘ totF) ~ id 
                H (pair α β) = tmp1 α (ptd α (mp x α β)) β
        
        contr1 : is-contr (Σ A (λ y → x ≡ y))
        contr1 = path-contr x

        contr2 : is-contr (Σ A (λ y → R x y))
        contr2 = retract-contr totF retract contr1

        fam-eq : (y : A) → is-equiv (fam x y)
        fam-eq = contr-family-equiv x contr2 (fam x)

judge-set : {i j : Level} {A : UU i} {R : A → A → UU j} → 
                (allp : (x y : A) → is-prop (R x y)) → 
                (ρ : (x : A) → R x x) → 
                (mp : (x y : A) → R x y → x ≡ y) → 
                (fam : (x y : A) → x ≡ y → R x y) → 
                is-set A 
judge-set {A = A} {R = R} allp ρ mp fam = is-p
    where
        tmp : (x y : A) → is-equiv (fam x y)
        tmp = Theorem10-2-3 allp ρ mp fam

        tmp1 : (x y : A) → (x ≡ y) ≃ R x y 
        tmp1 x y = pair (fam x y) (tmp x y)

        is-p : (x y : A) → is-prop(x ≡ y) 
        is-p x y = pr1 (homotopy-prop (homotopy-inv (tmp1 x y))) is-p'
            where
                is-p' : is-prop(R x y)
                is-p' = allp x y

-- Definition of injective
is-injective : {i j : Level} {A : UU i} {B : UU j} → 
                (f : A → B) → UU (i ⊔ j)
is-injective {A = A} f = (x y : A) → (f x ≡ f y) → x ≡ y

-- Theorem: Any injective map into a set is embedding
injective-map-to-set-isemb : {i j : Level} {A : UU i} {B : UU j} →
                             (f : A → B) → is-injective f → is-set B → 
                             is-emb f 
injective-map-to-set-isemb {j = j} {A = A} f f-inj B-set = fam-eq
    where
        R : A → A → UU j
        R x y = f x ≡ f y 

        R-refl : (x : A) → R x x
        R-refl x = refl

        R-prop : (x y : A) → is-prop (R x y)
        R-prop x y = B-set (f x) (f y)

        mp : (x y : A) → R x y → x ≡ y
        mp x y = f-inj x y
        
        fam : (x y : A) → x ≡ y → R x y 
        fam x y p = ap f p 

        fam-eq : (x y : A) → is-equiv(fam x y)
        fam-eq = Theorem10-2-3 R-prop R-refl mp fam

is-prop-prod : {i j : Level} {A : UU i} {B : UU j} → 
                is-prop A → is-prop B → is-prop (A × B)
is-prop-prod {j = j} {A = A} {B = B} A-is-prop B-is-prop = any-two-equiv-is-prop any-two-equiv
    where
        any-two-equiv : (r1 r2 : A × B) → r1 ≡ r2 
        any-two-equiv (pair x1 y1) (pair x2 y2) = (ap (pair x1) eq2) · (ap (λ z → pair z y2) eq1)
            where
                eq1 : x1 ≡ x2 
                eq1 = contr-center (A-is-prop x1 x2)

                eq2 : y1 ≡ y2
                eq2 = contr-center (B-is-prop y1 y2) 
        
