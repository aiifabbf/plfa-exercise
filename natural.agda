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

add-right-succ : forall (m n : Natural)
    -> Eq Natural (add m (succ n)) (succ (add m n))
add-right-succ 0 n = refl Natural (succ n)
add-right-succ (succ m') n = eq-congruence-input Natural Natural succ (add m' (succ n)) (succ (add m' n)) (add-right-succ m' n)

add-commutativity : forall (m n : Natural)
    -> Eq Natural (add m n) (add n m)
add-commutativity 0 n = eq-symmetricity Natural (add n 0) n (add-right-0 n)
add-commutativity (succ m') n = eq-transitivity Natural (succ (add m' n)) (succ (add n m')) (add n (succ m')) (eq-congruence-input Natural Natural succ (add m' n) (add n m') (add-commutativity m' n)) (eq-symmetricity Natural (add n (succ m')) (succ (add n m')) (add-right-succ n m'))
