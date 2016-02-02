== denotes a setoid equality. We will assume that all values are Proper with respect to this relation, including function types.

Monad m
-------

    bindM   : m a -> (a -> m b) -> m b
    returnM : a -> m a
    ==      : Equals a => relation (m a)
    bindM (returnM x) f == f x
    bindM c returnM == c
    bindM (bindM c k) k' == bindM c (fun x => bindM (k x) k')


PredMonad m pm
--------------

    Monad m
    Monad pm
    liftP   : m a -> pm a
    forallP : (a -> pm b) -> pm b
    existsP : (a -> pm b) -> pm b
    -->>    : pm a -> pm a -> pm a
    |--     : Order a => relation (pm a)

(NOTE: Entailment takes an Order in case a itself has a notion of entailment,
 e.g., a = Prop or a = pm b for some b. For instance, if P |-- Q holds then we
 would want (returnP P) |-- (returnP Q), even though P == Q may not
 hold. Conversely, for PP : pm (pm a) and QQ : pm (pm a), if PP |-- QQ then we
 would expect join PP |-- join QQ, even if (join PP) == (join QQ) does not
 hold. That is, join is Proper for (|-- (Order:=|--)) ==> (|--). )

    forallP f |-- f a
    (forall x, P |-- f x) -> P |-- forallP f
    f a |-- existsP f
    (forall x, f x |-- P) -> existsP f |-- P
    P |-- (Q -->> R) <-> (P //\\ Q) |-- R -- Adjunction law for implication
    liftP (returnM x) == returnM x
    liftP (bind c k) == bindM (liftP c) (fun x => liftP (k x))


(Definable operations)

     //\\    : pm a -> pm a -> pm a -- definable from forallP
     \\//    : pm a -> pm a -> pm a -- definable from existsP
     x |= y  := liftP x |-- y


(Derivable entailment rules)

    P |-- Q -> P |-- R -> P |-- (Q //\\ R)
    (P //\\ Q) |-- P
    (P //\\ Q) |-- Q
    P |-- R -> Q |-- R -> (P \\// Q) |-- R
    P |-- (P \\// Q) 
    Q |-- (P \\// Q)

(Derivable rules about monad satisfaction)
    m |= forallP P <-> (forall x, (m |= P x))
    m |= (P //\\ Q) <-> (m |= P) /\ (m |= Q)
    (m |= Q x) -> (m |= existsP Q) -- Note the asymmetry
    (m |= P) \/ (m |= Q) -> m |= (P \\// Q) -- Note the asymmetry 


StateMonad S m
--------------

    getM : m S
    putM : S -> m ()
    bindM get (fun x => bindM get (fun y => f x y)) == bindM get (fun x => f x x)
    bindM get put == returnM ()
    bindM (put x) (fun _ => get) == bindM (put x) (fun _ => returnM x)
    bindM (put x) (fun _ => put y) == put y


PredStateMonad S m pm
--------------------

    liftP getM == getM
    liftP (putM x) == putM

 (Both m and pm satisfy the StateMonad laws)
