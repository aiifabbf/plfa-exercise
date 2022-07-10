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

eq-transitivity : forall (T : Set)
    -> forall (m n p : T)
    -> Eq T m n
    -> Eq T n p
    -> Eq T m p
eq-transitivity T m n p (refl T n) (refl T n) = refl T n

LeibnizEq : forall (T : Set)
    -> forall (x y : T)
    -> Set1
LeibnizEq T x y = forall (p : T -> Set)
    -> p x
    -> p y

leibniz-eq-reflexivity : forall (T : Set)
    -> forall (x : T)
    -> LeibnizEq T x x
leibniz-eq-reflexivity T x = let
        helper : forall (T : Set)
            -> forall (x : T)
            -> forall (p : T -> Set)
            -> p x
            -> p x
        helper T x p t = t
    in
        helper T x
-- leibniz-eq-reflexivity T x p px = px

leibniz-eq-transitivity : forall (T : Set)
    -> forall (x y z : T)
    -> LeibnizEq T x y
    -> LeibnizEq T y z
    -> LeibnizEq T x z
leibniz-eq-transitivity T x y z x-eq-y y-eq-z p px = y-eq-z p (x-eq-y p px)
