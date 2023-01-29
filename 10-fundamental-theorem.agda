{-# OPTIONS --without-K --exact-split --safe #-}

module 10-fundamental-theorem where

import 09-contractible-types
open 09-contractible-types public

tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → 
        (f : (a : A) → B a → C a) → (Σ A B → Σ A C)
tot f (pair a x) = pair a (f a x) 


-- Lemma 9.1.2
fib-tot-equiv : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → 
                    (f : (a : A) → B a → C a) → (t : Σ A C) → 
                        fib (tot f) t ≃ fib (f (pr1 t)) (pr2 t)
fib-tot-equiv {A = A} {B = B} {C = C} f (pair a y) = pair F (pair F-section F-retraction)
    where
        F : (p : fib (tot f) (pair a y)) → fib (f a) y
        F (pair (pair a x) refl) = pair x refl 
        G : (p : fib (f a) y) → fib (tot f) (pair a y)
        G (pair x refl) = pair (pair a x) refl

        F-section : section F 
        F-section = pair G rua 
            where
                rua : (F ∘ G) ~ id 
                rua (pair x refl) = refl
        F-retraction : retraction F 
        F-retraction = pair G rua 
            where
                rua : (G ∘ F) ~ id 
                rua (pair (pair a x) refl) = refl


-- Theorem : Each map f in map family is equivalence <=> tot f is an equivalence
equiv-tot1 : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → 
                 (f : (a : A) → B a → C a) → 
                     map-is-contr (tot f) → ((a : A) → map-is-contr (f a))
equiv-tot1 {A = A} {B = B} {C = C} f totf-contr a y = tmp3
    where
        toty : Σ A C
        toty = pair a y 

        tmp : is-contr(fib (tot f) toty)
        tmp = totf-contr toty

        tmp2 : fib (tot f) toty ≃ fib (f a) y
        tmp2 = fib-tot-equiv f toty

        tmp3 : is-contr (fib (f a) y)
        tmp3 = contr-homotopy tmp2 tmp

equiv-tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → 
                (f : (a : A) → B a → C a) → 
                    (is-equiv (tot f)) → ((a : A) → is-equiv (f a))
equiv-tot f totf-equiv a = f-equiv
    where
        totf-contr : map-is-contr (tot f)
        totf-contr = equiv-map-is-contr (tot f) totf-equiv

        f-contr : map-is-contr (f a)
        f-contr = equiv-tot1 f totf-contr a

        f-equiv : is-equiv (f a)
        f-equiv = contr-map-is-equiv (f a) f-contr

-- Theorem : A is a type with a term (a : A), (f : (x : A) → (a ≡ x) → B x) is a family map,
--           Then ∀x, (f x) is equivalence if and only if (Σ A B) is contractible.
--           The proof is just the half.
contr-family-equiv : {i j : Level} {A : UU i} {B : A → UU j} → 
                            (a : A) → is-contr(Σ A B) → 
                            (f : (x : A) → (a ≡ x) → B x) → 
                                 (x : A) → is-equiv(f x)
contr-family-equiv {j = j} {A = A} {B = B} a contr f x = Fx-eq
    where
        totF : Σ A (λ α → a ≡ α) → Σ A B
        totF = tot f
        
        contr1 : is-contr (Σ A (λ α → a ≡ α))
        contr1 = path-contr a 
        
        contr2 : is-contr (Σ A B)
        contr2 = contr 

        G : Σ A B → Σ A (λ α → a ≡ α)
        G (pair x y) = pair a refl

        F-section : (totF ∘ G) ~ id 
        F-section (pair x y) = inv (eq2 · eq3)
            where
                cent1 : Σ A B 
                cent1 = pr1 contr2 

                eq1 : (r : Σ A B) → (cent1 ≡ r)
                eq1 = pr2 contr2

                eq2 : (pair x y) ≡ cent1
                eq2 = inv (eq1 (pair x y))

                eq3 : cent1 ≡ (pair a (f a refl))
                eq3 = eq1 (pair a (f a refl))

        F-retraction : (G ∘ totF) ~ id
        F-retraction (pair a refl) = refl

        totF-eq : is-equiv totF 
        totF-eq = pair (pair G F-section) (pair G F-retraction)

        Fx-eq : is-equiv (f x) 
        Fx-eq = equiv-tot f totF-eq x

        
-- Definition of embeddings
is-emb : {i j : Level} {A : UU i} {B : UU j} → 
            (f : A → B) → UU (i ⊔ j)
is-emb {A = A} f = (x y : A) → is-equiv (apf x y)
    where
        apf : (x y : A) → (x ≡ y) → (f x ≡ f y)
        apf x y p = ap f p


-- Theorem : equivalence is embeddings
equiv-is-emb : {i j : Level} {A : UU i} {B : UU j} → 
                  (f : A → B) → is-equiv f → is-emb f
equiv-is-emb {A = A} {B = B} f f-eq x y = apf-equiv y -- to prove : (y : A) → is-equiv(ap f)
    where
        f-has-inverse : has-inverse f 
        f-has-inverse = equiv-map-has-inverse f f-eq 

        g : B → A 
        g = pr1 f-has-inverse

        H1 : (f ∘ g) ~ id 
        H1 = pr2 (pr2 f-has-inverse)

        H2 : (g ∘ f) ~ id 
        H2 = pr1 (pr2 f-has-inverse)

        simeq : (Σ A (λ α → f x ≡ f α)) ≃ (Σ A (λ α → f α ≡ f x))
        simeq = pair G (pair G-section G-retraction)
            where
                G : (Σ A (λ α → f x ≡ f α)) → (Σ A (λ α → f α ≡ f x))
                G (pair y p) = pair y (inv p) 

                G-section : section G 
                G-section = pair F tmp 
                    where
                        F : (Σ A (λ α → f α ≡ f x)) → (Σ A (λ α → f x ≡ f α))
                        F (pair y p) = pair y (inv p)
                        
                        tmp : (G ∘ F) ~ id 
                        tmp (pair y p) = ap (pair y) (inv-inv p)
                G-retraction : retraction G 
                G-retraction = pair F tmp
                    where
                        F : (Σ A (λ α → f α ≡ f x)) → (Σ A (λ α → f x ≡ f α))
                        F (pair y p) = pair y (inv p)
                        
                        tmp : (F ∘ G) ~ id 
                        tmp (pair y p) = ap (pair y) (inv-inv p)
        
        contr1 : is-contr (Σ A (λ α → f α ≡ f x))
        contr1 = f-contr (f x) 
            where
                f-contr : map-is-contr f
                f-contr = equiv-map-is-contr f f-eq
        
        contr2 : is-contr (Σ A (λ α → f x ≡ f α))
        contr2 = contr-homotopy simeq1 contr1
            where
                simeq1 : (Σ A (λ α → f α ≡ f x)) ≃ (Σ A (λ α → f x ≡ f α))
                simeq1 = homotopy-inv simeq

        apf : (α : A) → (x ≡ α) → (f x ≡ f α)
        apf α p = ap f p

        apf-equiv : (α : A) → is-equiv (apf α)
        apf-equiv = contr-family-equiv x contr2 apf


