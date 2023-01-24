{-# OPTIONS --without-K --exact-split --safe #-}

module 09-contractible-types where

import 08-equivalences
open 08-equivalences public

-- Definition of contractible types
is-contr : {i : Level} → UU i → UU i
is-contr A = Σ A (λ a → (x : A) → a ≡ x)

contr-center : {i : Level} {A : UU i} → 
               is-contr A → A
contr-center = pr1

-- Proposition: all terms of a contractible type are equal
contr-eq : {i : Level} {A : UU i} → 
           is-contr A → (x y : A) → x ≡ y
contr-eq (pair a p) x y = (inv (p x)) · p y

-- Example: unit type is contractible
is-single : (x : unit) → star ≡ x
is-single star = refl

unit-is-contr : is-contr unit
unit-is-contr = pair star (λ x → is-single x)

-- Definition: fiber of a map
-- the fiber of f at b is the type of a: a that get mapped by f to b
fib : {i j : Level} {A : UU i} {B : UU j} → 
      (f : A → B) (b : B) → UU (i ⊔ j)
fib {A = A} f b = Σ A (λ x → (f x) ≡ b)

-- Definition: a map is said to be contractible if all its fibers are contractible
map-is-contr : {i j : Level} {A : UU i} {B : UU j} → 
               (f : A → B) → UU (i ⊔ j)
map-is-contr {B = B} f = (b : B) → is-contr (fib f b)
-- Think f is a map from space A to space B
-- Then f is contractible means that, for any element b in B,
-- The space A' ⊆ A that f(A') = b is contractible

-- Proposition: a contractible map has an inverse.
-- For any element b in B, the fiber of f at b is contractible
-- So we can find an element a in A that f(a) = b, where a is the center of the fiber
contr-map-inv : {i j : Level} {A : UU i} {B : UU j} → 
                 (f : A → B) → map-is-contr f → B → A
contr-map-inv f is-contr-f b = pr1 (contr-center (is-contr-f b))
-- is-contr-f b = is-contr (fib f b) means that the fiber of f at b is contractible
-- contr-center (is-contr-f b) : Σ A (λ x → (f x) ≡ b)

-- Proposition: a contractible map has a section.
contr-map-has-section : {i j : Level} {A : UU i} {B : UU j} → 
                         (f : A → B) → map-is-contr f → section f
contr-map-has-section f f-is-contr = pair g (λ y → pr2 (contr-center (f-is-contr y)))
    where
        g = contr-map-inv f f-is-contr
-- g = contr-map-inv f f-is-contr
-- g y = pr1 (contr-center (f-is-contr y)) : A
-- pr2 (contr-center (f-is-contr y)) : (f (g y)) ≡ y

-- pr2 (fib f b) : f (pr1 (fib f b)) ≡ b


-- Proposition: a contraictible map has a retraction

contr-map-has-retraction-tmp : {i j : Level} {A : UU i} {B : UU j} → 
                                (f : A → B) → (x : A) → (f-is-contr : map-is-contr f) → 
                                    pr1 (pr1 (f-is-contr (f x))) ≡ x
contr-map-has-retraction-tmp f x f-is-contr = ap pr1 (fib-eq (pair x refl))
    where
        fib-center = pr1 (f-is-contr (f x)) -- fib-center = pair y (t : f y ≡ f x)
        fib-eq = pr2 (f-is-contr (f x))     -- fib-eq = λ r → (pair y t ≡ r)
--   f-is-contr (f x)
-- = is-contr (fib f (f x))
-- = is-contr (Σ (y : A) (λ y → f y ≡ f x))
-- pr1 (f-is-contr (f x)) = pair y (t : f y ≡ f x) = fib-center
-- pr2 (f-is-contr (f x)) = λ r → (pair y t ≡ r)   = fib-eq

contr-map-has-retraction : {i j : Level} {A : UU i} {B : UU j} → 
                               (f : A → B) → map-is-contr f → retraction f
contr-map-has-retraction f f-is-contr = pair g (λ x → (contr-map-has-retraction-tmp f x f-is-contr))
    where
        g = contr-map-inv f f-is-contr

-- Proposition: Contractible maps are equivalent (Bilatural map)
contr-map-is-equiv : {i j : Level} {A : UU i} {B : UU j} → 
                        (f : A → B) → map-is-contr f → is-equiv f
contr-map-is-equiv f f-is-contr = pair (contr-map-has-section f f-is-contr) (contr-map-has-retraction f f-is-contr)


equiv-is-homotopy : {i j : Level} {A : UU i} {B : UU j} → 
                        (f : A → B) → (g1 g2 : B → A) → 
                        ((f ∘ g1) ~ id) → ((g2 ∘ f) ~ id) → g1 ~ g2
equiv-is-homotopy f g1 g2 H1 H2 b = p4 · p2
    where
        p1 = H1 b      -- f (g1 b) ≡ b
        p2 = ap g2 p1  -- g2 (f (g1 b)) ≡ g2 b
        p3 = H2 (g1 b) -- g2 (f (g1 b)) ≡ g1 b
        p4 = inv p3


-- Definition 8.3.3
nat-homotopy : {i j : Level} {A : UU i} {B : UU j} → 
                (x y : A) → (f g : A → B) → (H : f ~ g) → (p : x ≡ y) → 
                ((H x) · (ap g p)) ≡ ((ap f p) · (H y))
nat-homotopy x y f g H refl = right-unit (H x)



homotopy-ap : {i : Level} {A : UU i} → 
               (f : A → A) → 
               (H : f ~ id) → (x : A) → H (f x) ≡ (ap f (H x))
homotopy-ap {A = A} f H x = tmp8
    where
        tmp : inv (ap id (H x)) ≡ inv (H x)
        tmp = ap inv (inv (ap-id {B = A} (H x)))

        tmp1 : {a b c : A} {a1 a2 : a ≡ b} {b1 b2 : b ≡ c} → 
                (a1 ≡ a2) → (b1 ≡ b2) → (a1 · b1) ≡ (a2 · b2)
        tmp1 refl refl = refl

        tmp2 : (((H (f x)) · (ap id (H x))) · (inv (ap id (H x)))) ≡ (((ap f (H x)) · (H x)) · (inv (H x)))
        tmp2 = tmp1 (nat-homotopy (f x) x f id H (H x)) tmp

        tmp3 : ((H (f x)) · ((ap id (H x)) · (inv (ap id (H x))))) ≡ ((ap f (H x)) · ((H x) · (inv (H x))))
        tmp3 = ((inv (assoc p q r)) · tmp2) · (assoc p1 q1 r1)
            where
                p = H (f x)
                q = ap id (H x)
                r = inv (ap id (H x))
                p1 = ap f (H x)
                q1 = H x
                r1 = inv (H x)
        
        tmp4 : ((ap id (H x)) · (inv (ap id (H x)))) ≡ refl
        tmp4 = inv-concat (ap id (H x))

        tmp5 : H (f x) ≡ ((H (f x)) · ((ap id (H x)) · (inv (ap id (H x)))))
        tmp5 = (inv (right-unit (H (f x)))) · (tmp1 refl (inv tmp4))
        
        tmp6 : ((H x) · (inv (H x))) ≡ refl 
        tmp6 = inv-concat (H x)

        tmp7 : ((ap f (H x)) · ((H x) · (inv (H x)))) ≡ ((ap f (H x)))
        tmp7 = (ap (λ α → (ap f (H x)) · α) tmp6) · (right-unit (ap f (H x)))

        tmp8 : H (f x) ≡ (ap f (H x))
        tmp8 = (tmp5 · tmp3) · tmp7
        

-- Lemma 8.3.5
has-inverse-is-coh-invertible : {i j : Level} {A : UU i} {B : UU j} → 
                                (f : A → B) → (f-has-inverse : has-inverse f) →
                                let 
                                    g = pr1 f-has-inverse
                                    H = pr1 (pr2 f-has-inverse)
                                    G = pr2 (pr2 f-has-inverse)
                                in 
                                    Σ ((f ∘ g) ~ id) (λ G1 → ((G1 ·r f) ~ (f ·l H)))
has-inverse-is-coh-invertible {A = A} f f-has-inverse = pair G1 G1-eq7
    where
        -- ∃G1, (G1 ·l f) ~ (f ·r H)
        -- H : g ∘ f ~ id 
        -- G : f ∘ g ~ id
        g = pr1 f-has-inverse
        H = pr1 (pr2 f-has-inverse)
        G = pr2 (pr2 f-has-inverse)
        G1 : (f ∘ g) ~ id
        G1 y = (inv (G (f (g y)))) · ((ap f (H (g y))) · (G y))

        -- to prove : G1 ·r f(x) ≡ f ·l H(x)
        -- G1 ·r f(x) =  G^-1(fgf(x)) · (ap f (H(gf(x)))) · G(f(x))
        -- f ·l H(x) = ap f H(x)
        -- to prove : G(fgf(x)) · (ap f H(x)) ≡ (ap f (H (gf(x)))) · G(f(x))
        -- ap f (H gf(x)) = ap (fgf) H(x)
        G1-eq1 : (x : A) → ((G (f (g (f x)))) · (ap f (H x))) ≡ (((ap (f ∘ (g ∘ f)) (H x))) · (G (f x)))
        G1-eq1 x = nat-homotopy (g (f x)) x (f ∘ (g ∘ f)) f (G ·r f) (H x)

        G1-eq2 : (x : A) → (ap f (H (g (f x)))) ≡ (ap (f ∘ (g ∘ f)) (H x))
        G1-eq2 x = tmp2
             where
                 tmp1 : (ap f (H (g (f x)))) ≡ (ap f (ap (g ∘ f) (H x)))
                 tmp1 = ap (λ α → ap f α) (homotopy-ap (g ∘ f) H x)
                 tmp2 : (ap f (H (g (f x)))) ≡ (ap (f ∘ (g ∘ f)) (H x))
                 tmp2 = tmp1 · (ap-comp (g ∘ f) f (H x))
        
        G1-eq3 : (x : A) → ((G (f (g (f x)))) · (ap f (H x))) ≡ (((ap f (H (g (f x))))) · (G (f x)))
        G1-eq3 x = (G1-eq1 x) · (ap (λ β → β · (G (f x))) (inv (G1-eq2 x)))
        
        G1-eq4 : (x : A) → ((ap f (H x)) ≡ ((inv (G (f (g (f x))))) · (((ap f (H (g (f x))))) · (G (f x)))))
        G1-eq4 x = (tmp · (assoc (inv (G (f (g (f x))))) (G (f (g (f x)))) (ap f (H x)))) · (ap (λ α → (inv (G (f (g (f x))))) · α) (G1-eq3 x))
            where
                tmp : (ap f (H x)) ≡ (((inv (G (f (g (f x))))) · (G (f (g (f x))))) · (ap f (H x)))
                tmp = ap (λ β → β · (ap f (H x))) (inv (concat-inv (G (f (g (f x))))))
        
        G1-eq5 : (x : A) → (f ·l H) x ≡ (ap f (H x))
        G1-eq5 x = refl

        G1-eq6 : (x : A) → (G1 ·r f) x ≡ ((inv (G (f (g (f x))))) · (((ap f (H (g (f x))))) · (G (f x))))
        G1-eq6 x = refl

        G1-eq7 : (G1 ·r f) ~ (f ·l H)
        G1-eq7 x = inv (((G1-eq5 x) · (G1-eq4 x)) · (G1-eq6 x))

-- Definition of fib equality
fib-eq : {i j : Level} {A : UU i} {B : UU j} → 
            (f : A → B) → (y : B) →
                fib f y → fib f y → UU (i ⊔ j)
fib-eq f y s t = Σ (pr1 s ≡ pr1 t) (λ α → ((pr2 s) ≡ ((ap f α) · (pr2 t))))

fib-eq-≡ : {i j : Level} {A : UU i} {B : UU j} → 
            (f : A → B) → (y : B) → 
                {s t : fib f y} →
                    (fib-eq f y s t) → (s ≡ t)
fib-eq-≡ f y {pair x p} {pair x1 p1} (pair refl refl) = refl


-- Proposition : equivalent maps have inverse
equiv-map-has-inverse : {i j : Level} {A : UU i} {B : UU j} → 
                            (f : A → B) → 
                                is-equiv f → has-inverse f 
equiv-map-has-inverse f f-is-equiv = pair g (pair tmp G)
    where
        f-has-section = pr1 f-is-equiv
        f-has-retraction = pr2 f-is-equiv
        g = pr1 f-has-section
        h = pr1 f-has-retraction
        G = pr2 f-has-section    -- p1 : (f ∘ g) ~ id
        H = pr2 f-has-retraction -- p2 : (h ∘ f) ~ id
        K : g ~ h 
        K y = (inv (H (g y))) · (ap h (G y)) 
        tmp : (g ∘ f) ~ id
        tmp x = (K (f x)) · (H x)

-- Proposition : coherently invertible map has contractible fibers
coh-invertible-is-contr : {i j : Level} {A : UU i} {B : UU j} → 
                            (f : A → B) → (g : B → A) → (G : (f ∘ g) ~ id) → (H : (g ∘ f) ~ id) → (K : (G ·r f) ~ (f ·l H)) →
                            (y : B) → is-contr (fib f y)
coh-invertible-is-contr {A = A} f g G H K y = pair fib-center (λ r → fib-eq-≡ f y (fib-eq' r))
    where
        fib-center = pair (g y) (G y)
        fib-eq' : (r : fib f y)  → (fib-eq f y fib-center r)
        fib-eq' (pair x refl) = pair (H x) (K' x) 
            where
                K' : (x : A) → (G (f x)) ≡ ((ap f (H x)) · refl) 
                K' x = (K x) · (inv (right-unit (ap f (H x))))
                
-- Proposition : equivalent maps are contractible
equiv-map-is-contr : {i j : Level} {A : UU i} {B : UU j} → 
                        (f : A → B) → 
                            is-equiv f → map-is-contr f 
equiv-map-is-contr f f-is-equiv y = coh-invertible-is-contr f (pr1 f-has-reverse) G (pr1 (pr2 f-has-reverse)) K y
    where
        f-has-reverse : has-inverse f
        f-has-reverse = equiv-map-has-inverse f f-is-equiv

        f-is-coh-invertible = has-inverse-is-coh-invertible f f-has-reverse
        G = pr1 f-is-coh-invertible
        K = pr2 f-is-coh-invertible