open import natural

data Leq : Natural -> Natural -> Set where
    zero_leq_n : forall (n : Natural)
        -> Leq 0 n

    succ_m_leq_succ_n : forall (m n : Natural)
        -> Leq m n
        -> Leq (succ m) (succ n)

leq-transitivity : forall (m n p : Natural)
    -> Leq m n
    -> Leq n p
    -> Leq m p
leq-transitivity 0 _ p _ _ = zero_leq_n p
leq-transitivity (succ m') (succ n') (succ p') (succ_m_leq_succ_n m' n' t1) (succ_m_leq_succ_n n' p' t2) = succ_m_leq_succ_n m' p' (leq-transitivity m' n' p' t1 t2)
