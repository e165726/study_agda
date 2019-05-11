module nat where 

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool
  
one = (suc zero)
two = (suc one)
three = (suc two)
four = (suc three)
five = (suc four)
six = (suc five)

-- 足し算
-- 2 + 1
_+_ : Nat -> Nat -> Nat
zero + y = y
suc x + y = suc (x + y)
  
-- 掛け算
_*_ : Nat -> Nat -> Nat
x * zero = zero 
x * suc(y) = x + (x * y) 

-- 引き算 
_-_ : Nat -> Nat -> Nat
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

-- 小なり
_≤_ : Nat -> Nat -> Bool
zero ≤ b = true
suc a ≤ zero = false
suc a ≤ suc b = a ≤ b

-- 割り算
{-# TERMINATING #-}
_/_ : Nat -> Nat -> Nat
zero / y = zero
suc x / zero = zero
suc x / suc y with (y ≤ x)
... | true = suc ((x - y) / suc y) 
... | false = zero

-- 割り算 2

-- Ex) case of 6 / 3
-- 6 2 2 0
-- 5 1 2 0
-- 4 0 2 0
-- 3 2 2 1
-- 2 1 2 1
-- 1 0 2 1
-- 0 2 2 2

div-helper : Nat -> Nat -> Nat -> Nat -> Nat
div-helper zero y1 y2 i = i
div-helper (suc x) zero y2 i = div-helper x y2 y2 (suc i)
div-helper (suc x) (suc y1) y2 i = div-helper x y1 y2 i 

div : Nat -> Nat -> Nat
div x zero = zero
div x (suc y) = div-helper (suc x) y y zero

-- イコール定義
data _==_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x == x

cong : {A B : Set} -> {x y : A} -> (f : A -> B) -> x == y -> f x == f y
cong f refl = refl

trans : {A : Set} -> {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

-- suc (a + b) == a + suc(b)の証明
add-suc : (a b : Nat) -> suc (a + b) == (a + (suc b))
add-suc zero b = refl
add-suc (suc a) b = cong suc (add-suc a b)

-- 加法が可換であることの証明
add-comm : (x y : Nat) -> (x + y) == (y + x)
add-comm zero zero = refl
add-comm zero (suc y) = cong suc (add-comm zero y) 
add-comm (suc x) y = trans (cong suc (add-comm x y)) (add-suc y x)

-- TODO: 
-- suc (x + (y + z)) == ((suc x + (y + z))の証明
add-assoc-lemma : (x y z : Nat) -> suc (x + (y + z)) == ((suc x + (y + z))
add-assoc-lemma zero y z = refl
add-assoc-lemma (suc x) y z = cong suc (add-assoc-lemma x y z)

-- 加法の結合則 証明
add-assoc : (x y z : Nat) -> ((x + y) + z) ≡(x + (y + z))
add-assoc zero y z = refl
add-assoc (suc x) y z = trans (cong suc (add-assoc x y z)) (add-assoc-lemma x y z)

-- (sac x) * y ≡y + (y * x)の証明
mul-comm-lemma : (a b : Nat) -> (suc a * b) == (a + (a + b))
mul-comm-lemma zero zero = refl
-- mul-comm-lemma (suc a) b = cong suc (mul-lemma a b)

-- 乗法の可換則と結合則
mul-comm : (x y : Nat) -> (x * y) == (y * x)
mul-comm zero zero = refl
mul-comm zero (suc y) = mul-comm zero y
-- mul-comm (suc x) y = trans (cong suc (mul-comm x y)) (mul-comm-lemma y x) 
-- : (x y : Nat) -> (x * y) == (y * x)
-- mul-comm (sac x) y = x + (x * y)  
-- x * suc(y) = x + (x * y)
-- mul-comm x y = ?
