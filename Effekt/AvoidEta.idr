module Effekt.AvoidEta

import Effekt.CpsUnstaged
import public Effekt.CpsStaged
import public Effekt.IteratedUnstaged

mutual
  public export
  data CTX : List Type -> Type -> Type -> Type where
    Static :   (Exp a -> STM rs b)   -> CTX rs a b
    Dynamic :  Exp (a -> Stm rs b)   -> CTX rs a b

  -- data type to help with type inference
  -- bonus: can carry list of types around at runtime a bit less often
  public export
  data STM : List Type -> Type -> Type where
    Pure : Exp a -> STM [] a
    Iter : (CTX rs a r -> STM rs r) -> STM (r :: rs) a

unIter : STM (r :: rs) a -> CTX rs a r -> STM rs r
unIter (Iter m) = m

export
runPure : STM [] a -> Exp a
runPure (Pure x) = x

mutual
  export
  reify : STM rs a -> Exp (Stm rs a)
  reify (Pure m) = m
  reify (Iter m) =
    (Lam $ \ k =>  reify (m (Dynamic k)))

  export
  reflect : {rs : _} -> Exp (Stm rs a) -> STM rs a
  reflect {rs = []} m = Pure m
  reflect {rs = _ :: _} m =
    Iter $ \k => reflect (App (m)  ((reifyContext k)))

  export
  reifyContext : CTX rs a r -> Exp (a -> Stm rs r)
  reifyContext (Static k) = (Lam $ \ a =>  reify (k a))
  reifyContext (Dynamic k) = k

export
resume : {rs : _} -> CTX rs a r -> (Exp a -> STM rs r)
resume (Static k) = k
resume (Dynamic k) = \a => reflect (App (k)  (a))

export
pure : {rs : _} -> Exp a -> STM rs a
pure{  rs= []}         a = Pure a
pure{  rs= r :: rs}  a = Iter $ \k => resume k a

push : {r : _} -> {rs : _} -> CTX (r :: rs) a b -> CTX rs b r -> CTX rs a r
push f k = Static (\a => unIter (resume f a) k)

bind : {rs : _} -> STM rs a -> CTX rs a b -> STM rs b
bind (Pure m) f = resume f m
bind (Iter m) f = Iter $ \k => m (push f k)

export
shift0 : (CTX rs a r -> STM rs r) -> STM (r :: rs) a
shift0 = Iter

export
runIn0 : STM (r :: rs) a -> CTX rs a r -> STM rs r
runIn0 = unIter

export
reset0 : {rs : _} -> STM (a :: rs) a -> STM rs a
reset0 m = runIn0 m (Static AvoidEta.pure)

export
lift : {rs : _} -> STM rs a -> STM (r :: rs) a
lift = Iter . bind

export
(>>=) : {rs : _} -> STM rs a -> (Exp a -> STM rs b) -> STM rs b
m >>= f = bind m (Static f)

export
(>>) : {rs : _} -> STM rs a -> STM rs b -> STM rs b
m >> n = bind m (Static (const n))

add : {rs : _} -> STM rs Int -> STM rs Int -> STM rs Int
add mx my = AvoidEta.do
  x <- mx
  y <- my
  pure ((Add x y))

display : {rs : _} -> Exp String -> STM (IO () :: rs) ()
display {rs} s = shift0 (\c => AvoidEta.do
  a <- resume c Uni
  pure {rs} ((Seq ((Dis s)) a)))

export
displayTwice : STM [] (IO ())
displayTwice = reset0 {rs=[]} (
  (>>=) {rs=[IO ()]} (display {rs=[]} (Str "hello ")) (\u =>
  (>>=) {rs=[IO ()]} (display {rs=[]} (Str "world")) (\o =>
  pure {rs=[IO ()]} Ski)))

export
ifthenelse : Exp Bool -> STM rs a -> STM rs a -> STM rs a
ifthenelse {rs} Tru t _ = t
ifthenelse {rs} Fls _ e = e
ifthenelse b (Pure t) (Pure e) = Pure $ Ite b t e
ifthenelse b (Iter t) (Iter e) = Iter $ \k => ifthenelse b (t k) (e k)

export
letrec : {rs : _} -> ((Exp a -> STM rs b) -> Exp a -> STM rs b) -> Exp a -> STM rs b
letrec body a = reflect (App (Rec (\f => \x =>
  reify (body (\y => reflect (App (f)  (y))) x)))  (a))

-- Iteration happens to be recursion.
export
loop : {rs : _} -> (Exp a -> STM (r :: rs) a) -> Exp a -> STM rs r
loop m = letrec (\k => \a => unIter (m a) (Static k))

export
break : {rs : _} -> Exp r -> STM (r :: rs) a
break r = shift0 (\_ => AvoidEta.pure r)
