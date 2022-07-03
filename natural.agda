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
