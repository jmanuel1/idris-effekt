module Effekt.CpsATM

import Control.Applicative.Indexed
import Control.Functor.Indexed
import Control.Monad.Indexed

%default total

export
record Cps (a, r, o : Type) where
  constructor MkCps
  runCps : (a -> o) -> r

shift0 : ((a -> o) -> r) -> Cps a r o
shift0 = MkCps

runIn0 : Cps a r o -> (a -> o) -> r
runIn0 = runCps

reset0 : Cps o r o -> r
reset0 m = runIn0 m id

push : (a -> Cps b r o) -> (b -> o) -> (a -> r)
push f k = \a => runCps (f a) k

IndexedFunctor Type Type Cps where
  map f (MkCps m) = MkCps $ \k => m (k . f)

IndexedApplicative Type Cps where
  pure a = MkCps $ \k => k a
  ap (MkCps mf) (MkCps ma) = MkCps $ \k => mf $ \f => ma $ \a => k (f a)

IndexedMonad Type Cps where
  bind m f = MkCps $ \k => runCps m (push f k)
  join mm = bind mm id

-- I looked the Agda stdlib to get the type right.
-- https://www.cse.chalmers.se/~nad/listings/lib-0.7/Category.Monad.Continuation.html
shift : ((a -> o) -> Cps q p q) -> Cps a p o
shift m = shift0 (\k => reset0 (m k))

-- Example from "Answer-Type Modification without Tears" by Kobori, Kameyama,
-- and Kiselyov.
-- https://arxiv.org/pdf/1606.06379
example : List Int
example =
  let append123 = reset0 (append [1, 2, 3])
  in append123 [4, 5, 6] where
    append : List Int -> Cps (List Int) (List Int -> List Int) (List Int)
    append [] = shift (\k => pure k)
    append (x :: xs) = map (x ::) $ append xs

test : CpsATM.example = [1, 2, 3, 4, 5, 6]
test = Refl
