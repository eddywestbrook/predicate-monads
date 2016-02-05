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
*GM* this makes sense to me now. This ordering is the computation ordering.

*Rules for logical operators*

    forallP f |-- f a
    (forall x, P |-- f x) -> P |-- forallP f
    f a |-- existsP f
    (forall x, f x |-- P) -> existsP f |-- P
    P |-- (Q -->> R) <-> (P //\\ Q) |-- R -- Adjunction law for implication

*Rules for liftP*

    liftP (returnM x) == returnM x
    liftP (bind c k) == bindM (liftP c) (fun x => liftP (k x))

*Rules for commuting logical operators with bind*

    (forallP P) >>= Q == forallP (fun x => P x >>= Q)
    P >>= (fun x => forallP (Q x)) == forallP (fun y => P >>= fun x => Q x y)
    (existsP P) >>= Q == existsP (fun x => P x >>= Q)
    P >>= (fun x => existsP (Q x)) == existsP (fun y => P >>= fun x => Q x y)
    (P1 -->> P2) >>= Q == (P1 >>= Q) -->> (P2 >>= Q)
    P >>= (fun x => Q1 x -->> Q2 x) == (P1 >>= Q) --> (P2 >>= Q)

*Definable operations*

     //\\    : pm a -> pm a -> pm a -- definable from forallP
     \\//    : pm a -> pm a -> pm a -- definable from existsP
     assertP : Prop -> pm a -- definable from existsP
     x |= y  := liftP x |-- y

*Derivable entailment rules*

    P |-- Q -> P |-- R -> P |-- (Q //\\ R)
    (P //\\ Q) |-- P
    (P //\\ Q) |-- Q
    P |-- R -> Q |-- R -> (P \\// Q) |-- R
    P |-- (P \\// Q) 
    Q |-- (P \\// Q)
    (phi -> trueP |-- P) -> assertP phi |-- P
    phi -> P  |-- assertP phi

*Derivable rules about monad satisfaction*

    m |= forallP P <-> (forall x, (m |= P x))
    m |= (P //\\ Q) <-> (m |= P) /\ (m |= Q)
    (m |= Q x) -> (m |= existsP Q) -- Note the asymmetry
    (m |= P) \/ (m |= Q) -> m |= (P \\// Q) -- Note the asymmetry 


StateMonad S m
--------------

    getM : m S
    putM : S -> m ()
    bindM getM (fun _ => m) == m
    bindM getM putM == returnM ()
    bindM (putM x) (fun _ => getM) == bindM (putM x) (fun _ => returnM x)
    bindM (putM x) (fun _ => putM y) == putM y


PredStateMonad S m pm
---------------------

    liftP getM == getM
    liftP (putM x) == putM x

 (Both m and pm satisfy the StateMonad laws)
 
 
*GM* What is the concrete instance for the standard state monad?

*EW* NOTE: technically it is pm T := S -> T * S -> Prop, since it is built from
StateT (SetM), but this is morally equivalent to the below

     m T  := S -> (T * S)
     Monad m -- standard instance
     pm T := S -> T -> S -> Prop
     Monad pm
       returnM x := fun st res st' => st = st' /\ x = res
       bindM   c k := fun st res st'' => exists res' st', c st res' st' /\ (k res') st' res st''
       liftP c := fun st res st' => c st = (res, st')
       forallP P := fun st res st' => forall x, P x st res st'
       existsP P := fun st res st' => exists x, P x st res st'
       P -->> Q  := fun st res st' => P st res st' -->> Q st res st'
       P |-- Q   := foral st res res' st', res < res' -> P st res st' -> Q st res st'
     MonadState pm
       getM := fun st res st' => st = st' /\ res = st'
       putM x := fun _ res st' => res = tt /\ x = st'
 
 

Intra-monad Reasoning
---------------------

Defining Hoare logic:

    hoareP (pre: S -> Prop) (post: A -> S -> Prop) : PM A :=
        (getP >>= fun st => assertP (pre st)) -->>
        (trueP >>= fun res => getP >>= fun st' =>
            andP (assertP (post res st')) (returnP res))

Theorem:
**forall m pre post,
    (forall st, pre st ->
        (putP st >> liftP m) |--
        (do
            putP st;
            res <- liftP m;
            st' <- getP;
            andP (assertP (post res st')) (returnP res))) ->
    m |= hoareP pre post**

Some basic examples written as 'hoare logic formulas'

**forall x, { fun st => st = x } getM { fun result st => st = x /\ result = x }**

    forall x, getM |= hoareP (fun st => st = x) (fun result st => st = x /\ result = x)

*Proof*

    st = x ->
    (putP st >> getP) |--
    (do
        putP st;
        res <- getP;
        st' <- getP;
        andP (assertP (st' = x /\ res = x)) (returnP res))

By rewriting using st = x:

    (putP x >> getP) |--
    (do
        putP x;
        res <- getP;
        st' <- getP;
        andP (assertP (st' = x /\ res = x)) (returnP res))

By state monad laws:

    (putP x >> returnP x) |--
    (do
        putP x;
        andP (assertP (x = x /\ x = x)) (returnP x))

By assertP introduction, proper-ness, and the law "andP trueP P = P":

    (putP x >> returnP x) |-- (putP x >> returnP x)

Q.E.D. by reflexivity.


*GM* what is the right way to assert facts? This seems somewhat unnatural. Is there a better way to write this?

Other examples:

    { True } modifyM (mult 2) { fun _ st => Even st }
    { True } tryM (raiseM 3) returnM { fun result => result = 3 } -- succeeds and result is 3


Running Monads
--------------

Eventually, we want to be able to conclude something from running a monadic computation. For example,

    { P } c { Q }
    -------------------
    runState c x = y -> (P x -> Q y)
    
Does this come from unfolding the definition of |--?
