open import eq

data Natural : Set where
    zero : Natural
    succ : Natural -> Natural

{-# BUILTIN NATURAL Natural #-}

add : Natural -> Natural -> Natural
add 0 n = n
add (succ m') n = succ (add m' n)

1-add-1-equal-2 : Eq Natural (add 1 1) 2
1-add-1-equal-2 = refl Natural 2

add-associativity : forall (m n p : Natural)
    -> Eq Natural (add (add m n) p) (add m (add n p))
add-associativity 0 n p = refl Natural (add n p)
add-associativity (succ m') n p = eq-congruence-input Natural Natural succ (add (add m' n) p) (add m' (add n p)) (add-associativity m' n p)

add-right-0 : forall (m : Natural)
    -> Eq Natural (add m 0) m
add-right-0 0 = refl Natural 0
add-right-0 (succ m') = eq-congruence-input Natural Natural succ (add m' 0) m' (add-right-0 m')
