{-# OPTIONS --without-K --exact-split --safe #-}
module 04-inductive where

import 03-naturals
open 03-naturals public

-- Definition 4.2.1
data unit : UU lzero where
    star : unit

𝟙 = unit

ind-unit : {i : Level} {P : 𝟙 → UU i} → P star → ((x : 𝟙) → P x)
ind-unit p star = p

-- Definition 4.3.1
data empty : UU lzero where

𝟘 = empty

ind-empty : {i : Level} {P : 𝟘 → UU i} → ((x : 𝟘) → P x)
ind-empty ()

ex-falso : {i : Level} {A : UU i} → 𝟘 → A
ex-falso = ind-empty

-- Definition 4.3.2
¬ : {i : Level} → UU i → UU i
¬ A = A → 𝟘

-- Proposition 4.3.3
functor-neg : {i1 i2 : Level} {P : UU i1} {Q : UU i2} → (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)

-- Definition 4.4.1
data bool : UU lzero where
    true  : bool
    false : bool

𝔹 = bool

-- Example 4.4.2
neg-bool : 𝔹 → 𝔹
neg-bool true = false
neg-bool false = true

conjunction : 𝔹 → 𝔹 → 𝔹
conjunction true true = true
conjunction true false = false
conjunction false true = false
conjunction false false = false

-- Definition 4.5.1
data coprod {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j) where
    inl : A → coprod A B
    inr : B → coprod A B

_∔_ = coprod

ind-coprod : {i j k : Level} {A : UU i} {B : UU j} (P : A ∔ B → UU k) → 
             ((x : A) → P (inl x)) → 
             ((y : B) → P (inr y)) → 
             ((t : A ∔ B) → P t)
ind-coprod P f g (inl x) = f x
ind-coprod P f g (inr y) = g y

-- Remark 4.5.2
functor-coprod : {i1 i2 j1 j2 : Level} {A : UU i1} {B : UU i2} {A' : UU j1} {B' : UU j2} → (A → A') → (B → B') → ((A ∔ B) → (A' ∔ B'))
functor-coprod f g (inl x) = inl (f x)
functor-coprod f g (inr y) = inr (g y) 

-- Proposition 4.5.3
coprod-elim-left : {i j : Level} {A : UU i} {B : UU j} → ¬ B → A ∔ B → A
coprod-elim-left nb (inl x) = x
coprod-elim-left nb (inr y) = ex-falso (nb y)

coprod-elim-right : {i j : Level} {A : UU i} {B : UU j} → ¬ A → A ∔ B → B
coprod-elim-right na (inl x) = ex-falso (na x)
coprod-elim-right na (inr y) = y

-- Definition 4.6.1
data Σ {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
    pair : (x : A) → (B x → Σ A B)


_⋆_ = Σ

ind-Σ : {i j k : Level} {A : UU i} {B : A → UU j} → (P : A ⋆ B → UU k) → ((x : A) (y : B x) → P (pair x y)) → ((t : A ⋆ B) → P t)
ind-Σ P f (pair x y) = f x y

-- Remark 4.6.2
ev-pair : {i j k : Level} {A : UU i} {B : A → UU j} (P : A ⋆ B → UU k) → ((t : A ⋆ B) → P t) → ((x : A) (y : B x) → P (pair x y))
ev-pair P f x y = f (pair x y)         


-- Definition 4.6.3
pr1 : {i j : Level} {A : UU i} {B : A → UU j} → A ⋆ B → A
pr1 (pair a b) = a

pr2 : {i j : Level} {A : UU i} {B : A → UU j} → (t : A ⋆ B) → B (pr1 t) 
pr2 (pair a b) = b

-- Definition 4.6.4
prod : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
prod A B = A ⋆ (λ a → B)

_×_ = prod


-- Definition 4.7.1
ℤ : UU lzero
ℤ = ℕ ∔ (𝟙 ∔ ℕ)

in-neg : ℕ → ℤ
in-neg n = inl n

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ

zero-ℤ : ℤ
zero-ℤ = inr (inl star)

one-ℤ : ℤ
one-ℤ = inr (inr zero-ℕ)

in-pos : ℕ → ℤ
in-pos n = inr (inr n)

int-ℕ : ℕ → ℤ
int-ℕ zero-ℕ = zero-ℤ
int-ℕ (succ-ℕ n) = in-pos n

ind-ℤ : {i : Level} (P : ℤ → UU i) → 
    P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
    P zero-ℤ →
    P one-ℤ → ((n : ℕ) → P (inr (inr n)) → P (inr (inr (succ-ℕ n)))) →
    (n : ℤ) → P n
ind-ℤ P pn1 indn p0 p1 ind (inr (inl star)) = p0
ind-ℤ P pn1 indn p0 p1 ind (inl zero-ℕ) = pn1
ind-ℤ P pn1 indn p0 p1 ind (inl (succ-ℕ n)) = indn n (ind-ℤ P pn1 indn p0 p1 ind (inl n))
ind-ℤ P pn1 indn p0 p1 ind (inr (inr zero-ℕ)) = p1
ind-ℤ P pn1 indn p0 p1 ind (inr (inr (succ-ℕ n))) = ind n (ind-ℤ P pn1 indn p0 p1 ind (inr (inr n)))

-- Definition 4.7.3
succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ n)) = inl n
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr n)) = inr (inr (succ-ℕ n))

-- Exercise 4.1(a)
pred-ℤ : ℤ → ℤ
pred-ℤ (inl n) = inl (succ-ℕ n)
pred-ℤ (inr (inl star)) = neg-one-ℤ
pred-ℤ (inr (inr zero-ℕ)) = zero-ℤ
pred-ℤ (inr (inr (succ-ℕ n))) = inr (inr n)

-- Exercise 4.1(b)
add-ℤ : ℤ → ℤ → ℤ
add-ℤ (inl zero-ℕ) m = pred-ℤ m
add-ℤ (inl (succ-ℕ n)) m = pred-ℤ (add-ℤ (inl n) m)
add-ℤ (inr (inl star)) m = m
add-ℤ (inr (inr zero-ℕ)) m = succ-ℤ m
add-ℤ (inr (inr (succ-ℕ n))) m = succ-ℤ (add-ℤ (inr (inr n)) m)

neg-ℤ : ℤ → ℤ
neg-ℤ (inr (inl star)) = zero-ℤ
neg-ℤ (inr (inr n)) = inl n
neg-ℤ (inl n) = inr (inr n)

-- Exercise 4.1(c)
mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inr (inl star)) m = zero-ℤ
mul-ℤ (inl zero-ℕ) m = neg-ℤ m
mul-ℤ (inl (succ-ℕ n)) m = add-ℤ (neg-ℤ m) (mul-ℤ (inl n) m)
mul-ℤ (inr (inr zero-ℕ)) m = m
mul-ℤ (inr (inr (succ-ℕ n))) m = add-ℤ m (mul-ℤ (inr (inr n)) m)

-- Exercise 4.2(a)
_ : {i : Level} {A : UU i} → (p : A) → ¬ (¬ A)
_ = λ p inv → ex-falso (inv p) 

-- Exercise 4.8(a)
data list {i : Level} (A : UU i) : UU i where
  nil  : list A
  cons : A → list A → list A

ind-list : {i : Level} {A : UU i} → A → list A
ind-list a = cons a nil

-- Exercise 4.8(b)
fold-list : {i1 i2 : Level} {A : UU i1} {B : UU i2} → (b : B) → (μ : A → B → B) → list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = fold-list (μ a b) μ l

length-list : {i : Level} {A : UU i} → list A → ℕ
length-list nil = zero-ℕ
length-list (cons a l) = succ-ℕ (length-list l)

concat-list : {i : Level} {A : UU i} → list A → list A → list A 
concat-list nil b = b 
concat-list (cons a l) b = cons a (concat-list l b)

reverse-list : {i : Level} {A : UU i} → list A → list A 
reverse-list nil = nil
reverse-list (cons a l) = concat-list (reverse-list l) (ind-list a)

leq-ℕ : ℕ → ℕ → UU lzero 
leq-ℕ zero-ℕ m = 𝟙 
leq-ℕ (succ-ℕ n) zero-ℕ = 𝟘 
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m 

_<=_ = leq-ℕ


leq-excluded-middle-ℕ : {x y : ℕ} → 
                        (x <= y) ∔ (y <= x)
leq-excluded-middle-ℕ {zero-ℕ} {y} = inl star
leq-excluded-middle-ℕ {succ-ℕ x} {zero-ℕ} = inr star 
leq-excluded-middle-ℕ {succ-ℕ x} {succ-ℕ y} = leq-excluded-middle-ℕ {x} {y}

leq-three-ℕ' : {x y z : ℕ} → 
              ((x <= y) ∔ (y <= x)) → 
              ((x <= z) ∔ (z <= x)) → 
              ((y <= z) ∔ (z <= y)) → 
               ((x <= y) × (y <= z)) ∔
              (((x <= z) × (z <= y)) ∔
              (((y <= x) × (x <= z)) ∔
              (((y <= z) × (z <= x)) ∔
              (((z <= x) × (x <= y)) ∔
               ((z <= y) × (y <= x))))))
leq-three-ℕ' (inl a) (inl b) (inl c) = inl (pair a c)
leq-three-ℕ' (inl a) (inl b) (inr c) = inr (inl (pair b c))
leq-three-ℕ' (inl a) (inr b) (inl c) = inr (inr (inr (inl (pair c b))))
leq-three-ℕ' (inl a) (inr b) (inr c) = inr (inr (inr (inr (inl (pair b a)))))
leq-three-ℕ' (inr a) (inl b) (inl c) = inr (inr (inl (pair a b)))
leq-three-ℕ' (inr a) (inl b) (inr c) = inr (inr (inl (pair a b)))
leq-three-ℕ' (inr a) (inr b) (inl c) = inr (inr (inr (inl (pair c b))))
leq-three-ℕ' (inr a) (inr b) (inr c) = inr (inr (inr (inr (inr (pair c a)))))

leq-three-ℕ : {x y z : ℕ} → 
               ((x <= y) × (y <= z)) ∔
              (((x <= z) × (z <= y)) ∔
              (((y <= x) × (x <= z)) ∔
              (((y <= z) × (z <= x)) ∔
              (((z <= x) × (x <= y)) ∔
               ((z <= y) × (y <= x))))))
leq-three-ℕ {x} {y} {z} = leq-three-ℕ' {x} {y} {z}
                                       (leq-excluded-middle-ℕ {x} {y}) 
                                       (leq-excluded-middle-ℕ {x} {z}) 
                                       (leq-excluded-middle-ℕ {y} {z})