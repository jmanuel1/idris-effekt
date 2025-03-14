module Effekt.CpsATM

%default total

export
record Cps (r, o, a : Type) where
  constructor MkCps
  runCps : (a -> o) -> r

shift0 : ((a -> o) -> r) -> Cps r o a
shift0 = MkCps

runIn0 : Cps r o a -> (a -> o) -> r
runIn0 = runCps

reset0 : Cps r o o -> r
reset0 m = runIn0 m id

pure : a -> Cps r r a
pure a = MkCps $ \k => k a

push : (a -> Cps r o b) -> (b -> o) -> (a -> r)
push f k = \a => runCps (f a) k

bind : Cps r o a -> (a -> Cps o p b) -> Cps r p b
bind m f = MkCps $ \k => runCps m (push f k)

(>>=) : Cps r o a -> (a -> Cps o p b) -> Cps r p b
m >>= f = bind m f

-- I looked the Agda stdlib to get the type right.
-- https://www.cse.chalmers.se/~nad/listings/lib-0.7/Category.Monad.Continuation.html
shift : ((a -> o) -> Cps p q q) -> Cps p o a
shift m = shift0 (\k => reset0 (m k))

Functor (Cps r o) where
  map f m = m >>= (pure . f)

-- Example from "Answer-Type Modification without Tears" by Kobori, Kameyama,
-- and Kiselyov.
-- https://arxiv.org/pdf/1606.06379
example : List Int
example =
  let append123 = reset0 (append [1, 2, 3])
  in append123 [4, 5, 6] where
    append : List Int -> Cps (List Int -> List Int) (List Int) (List Int)
    append [] = shift (\k => pure k)
    append (x :: xs) = map (x ::) $ append xs

test : CpsATM.example = [1, 2, 3, 4, 5, 6]
test = Refl
