{-# OPTIONS --without-K --exact-split --safe #-}
module 05-identity where

import 04-inductive
open 04-inductive public

-- Definition 5.1.1
-- Id, equivalent, path-connected
data _≡_ {i : Level} {A : UU i} (x : A) : A → UU i where
    refl : x ≡ x

-- let PTA = "path start at a", which is a type
-- ind-≡_a : given a PTA, P(PTA) is a proposition
-- The essence of induction is that ∀PTA, P(PTA) is proved iff. P(refl_a) is proved. 
-- since for any PTA, the only constructor is refl_a.
ind-≡ : {i j : Level} {A : UU i} {a : A} →
        (P : {x : A} → a ≡ x → UU j) →
        (p : P {a} refl) →
        ({x : A} (p : a ≡ x) → P p)
ind-≡ P p refl = p

-- Definition 5.2.1
_·_ : {i : Level} {A : UU i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl · q = q

-- Definition 5.2.2
inv : {i : Level} {A : UU i} {x y : A} → x ≡ y → y ≡ x
inv refl = refl

-- Definition 5.2.3
assoc : {i : Level} {A : UU i} {x y z w : A} → 
        (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
        ((p · q) · r) ≡ (p · (q · r))
assoc refl _ _ = refl

-- Definition 5.2.4
left-unit : {i : Level} {A : UU i} {x y : A} (p : x ≡ y) → (refl · p) ≡ p
left-unit refl = refl 

right-unit : {i : Level} {A : UU i} {x y : A} (p : x ≡ y) → (p · refl) ≡ p
right-unit refl = refl

-- Definition 5.2.5
left-inv : {i : Level} {A : UU i} {x y : A} (p : x ≡ y) → ((inv p) · p) ≡ refl
left-inv refl = refl

right-inv : {i : Level} {A : UU i} {x y : A} (p : x ≡ y) → (p · (inv p)) ≡ refl 
right-inv refl = refl 

-- Definition 5.3.1 action on path
ap : {i j : Level} {A : UU i} {B : UU j} {x y : A} → 
                   (f : A → B) → -- action 
                   (p : x ≡ y) → -- path
                   (f x) ≡ (f y) -- action on path
ap f refl = refl

ap-id : {i j : Level} {A : UU i} {B : UU j} {x y : A} → 
        (p : x ≡ y) → 
        p ≡ ap (λ a → a) p -- apply the Id function on path x = y
ap-id refl = refl

ap-comp : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} {x y : A} → 
          (f : A → B) → 
          (g : B → C) → 
          (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g refl = refl

ap-inv : {i j : Level} {A : UU i} {B : UU j} {x y : A} → 
         (f : A → B) → 
         (p : x ≡ y) →
         (ap f (inv p)) ≡ inv (ap f p)
ap-inv f refl = refl

-- Definition 5.4.1
tr : {i j : Level} {A : UU i} {x y : A} {B : A → UU j} →
     (p : x ≡ y) → 
     B x → B y
tr refl b = b

-- Definition 5.4.2
apd : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} →
      (f : (a : A) → B a)
      (p : x ≡ y) → 
      tr p (f x) ≡ f y
apd f refl = refl      

-- Proposition 5.6.1
right-unit-law-add-ℕ :
        (n : ℕ) → (add-ℕ n zero-ℕ) ≡ n
right-unit-law-add-ℕ n = refl

left-unit-law-add-ℕ :
        (n : ℕ) → (add-ℕ zero-ℕ n) ≡ n 
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ n) = ap succ-ℕ (left-unit-law-add-ℕ n) 

-- Proposition 5.6.2
left-successor-law-add-ℕ :
        (n m : ℕ) → (add-ℕ (succ-ℕ n) m) ≡ (succ-ℕ (add-ℕ n m))
left-successor-law-add-ℕ n zero-ℕ = refl  
left-successor-law-add-ℕ n (succ-ℕ m) = refl · ap succ-ℕ (left-successor-law-add-ℕ n m)

right-successor-law-add-ℕ :
        (n m : ℕ) → (add-ℕ n (succ-ℕ m)) ≡ (succ-ℕ (add-ℕ n m))
right-successor-law-add-ℕ n m = refl

-- Proposition 5.6.3
associative-add-ℕ : 
        (a b c : ℕ) → (add-ℕ (add-ℕ a b) c) ≡ (add-ℕ a (add-ℕ b c))
associative-add-ℕ a b zero-ℕ = refl
associative-add-ℕ a b (succ-ℕ c) = refl · ap succ-ℕ (associative-add-ℕ a b c)

commutative-add-ℕ :
        (n m : ℕ) → (add-ℕ n m) ≡ (add-ℕ m n)
commutative-add-ℕ n zero-ℕ = (right-unit-law-add-ℕ n) · (inv (left-unit-law-add-ℕ n))
commutative-add-ℕ n (succ-ℕ m) = (ap succ-ℕ (commutative-add-ℕ n m)) · (inv (left-successor-law-add-ℕ m n)) 

-- Exercise 5.2
distribute-inv-concat : {i : Level} {A : UU i} {x y z : A} → 
                        (p : x ≡ y) → 
                        (q : y ≡ z) → 
                        (inv (p · q)) ≡ ((inv q) · (inv p))
distribute-inv-concat refl refl = refl

-- Exercise 5.4
lift : {i j : Level} {A : UU i} {B : A → UU j} {x x1 : A} → 
       (p : x ≡ x1) → 
       (y : B x) → 
       (pair x y) ≡ (pair x1 (tr {B = B} p y))
lift refl y = refl


 