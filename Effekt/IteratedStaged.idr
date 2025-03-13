module Effekt.IteratedStaged

import Effekt.CpsStaged
import Effekt.IteratedUnstaged

STM : List Type -> Type -> Type
STM [] a = Exp a
STM (r :: rs) a = (Exp a -> STM rs r) -> STM rs r

pure : {rs : _} -> Exp a -> STM rs a
pure{  rs= []}         a = a
pure{  rs= r :: rs}  a = \k => k a

push : (Exp a -> STM (r :: rs) b) -> (Exp b -> STM rs r) -> (Exp a -> STM rs r)
push f k = \a => f a k

bind : {rs : _} -> STM rs a -> (Exp a -> STM rs b) -> STM rs b
bind{  rs= []}         m f = f m
bind{  rs= r :: rs}  m f = \k => m (push f k)

(>>=) : {rs : _} -> STM rs a -> (Exp a -> STM rs b) -> STM rs b
(>>=) = bind

lift : {r : _} -> {rs : _} -> STM rs a -> STM (r :: rs) a
lift = bind

shift0 : {r : _} -> {rs : _} -> ((Exp a -> STM rs r) -> STM rs r) -> STM (r :: rs) a
shift0 = id

runIn0 : {r : _} -> {rs : _} -> STM (r :: rs) a -> (Exp a -> STM rs r) -> STM rs r
runIn0 = id

reset0 : {a : _} -> {rs : _} -> STM (a :: rs) a -> STM rs a
reset0 m = runIn0 m IteratedStaged.pure

mutual
  reify : {rs : _} -> STM rs a -> Exp (Stm rs a)
  reify {rs = []} m = m
  reify {rs = (q :: qs)} m =
    (Lam $ \ k =>  reify (m (\a => reflect {a = q} {rs = qs} (App k  a))))

  reflect : {rs : _} -> Exp (Stm rs a) -> STM rs a
  reflect {rs = []} m = m
  reflect {rs = (q :: qs)} m =
    \k => reflect (App m  ((Lam $ \ a =>  reify (k a))))

emit : {rs : _} ->  Exp Int -> STM (List Int :: rs) ()
emit {rs} a = shift0 (\c => IteratedStaged.do
  as <- c Uni
  pure {rs} (Con a as))

emitTwice : {rs : _} -> Exp Int -> STM (List Int :: List Int :: rs) ()
emitTwice {rs} a =
  bind {rs=List Int::List Int::rs} (emit {rs=List Int::rs} a) (\u =>
  lift {r=List Int} {rs=List Int::rs} (emit a))

export
reifiedEmitTwice : Exp (Int -> Stm [List Int,List Int] ())
reifiedEmitTwice = Lam (\x => reify {rs=[List Int,List Int]} (emitTwice {rs = []} x))

export
reifiedEmitTwice' : Exp (Int -> Stm [List Int,List Int,()] ())
reifiedEmitTwice' = Lam (\x => reify {rs=[List Int,List Int,()]} (emitTwice {rs=[()]} x))
