data Eq : forall (T : Set) -> T -> T -> Set where
    refl : forall (T : Set)
        -> forall (x : T)
        -> Eq T x x

eq-symmetricity : forall (T : Set)
    -> forall (x y : T)
    -> Eq T x y
    -> Eq T y x
eq-symmetricity T x y (refl T x) = refl T y

eq-congruence-input : forall (A B : Set)
    -> forall (f : A -> B)
    -> forall (x y : A)
    -> Eq A x y
    -> Eq B (f x) (f y)
eq-congruence-input A B f x y (refl A x) = refl B (f y)

eq-congruence-function : forall (A B : Set)
    -> forall (f g : A -> B)
    -> Eq (A -> B) f g
    -> forall (x : A)
    -> Eq B (f x) (g x)
-- eq-congruence-function A B f g (refl (A -> B) f) x = refl B (f x)
eq-congruence-function A B f g (refl _ f) x = refl B (f x)