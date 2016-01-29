Monad m
-------
 bindM   : m a -> (a -> m b) -> m b
 returnM : a -> m a
 ==      : relation a -> relation (m a)

 bindM (returnM x) f == f x
 bindM c returnM == c
 bindM (bindM c k) k' == bindM c (fun x => bindM (k x) k')

PredMonad m pm
--------------
 Monad m
 Monad pm
 liftP   : m a -> pm a
 forallP : (a -> pm b) -> pm b
 (* No existsP? *)
 -->>    : pm a -> pm a -> pm a
 //\\    : pm a -> pm a -> pm a       -- Defineable from forallP
 |--     : Order a => relation (pm a) -- Why do we need an order?
 x |= y  := liftP x |-- y

 liftP (returnM x) == returnM x
 liftP (bind c k) == bindM (liftP c) (fun x => liftP (k x))

 forallP f |-- f a
 (forall x, P |-- f x) -> P |-- forallP f
 (P //\\ Q) |-- P
 (P //\\ Q) |-- Q

StateMonad S m
--------------
 getM : m S
 putM : S -> m ()

 bindM get put = returnM ()
 bindM (put x) (fun _ => get) = bindM (put x) (fun _ => returnM x)
 