module Main

import Effekt.AvoidEta

fail : {rs : _} -> STM (String :: rs) a
fail = shift0 (\k => AvoidEta.do
  pure (Str "no"))

flip : {r : _} -> {rs : _} -> STM (r :: rs) Bool
flip = shift0 (\k => AvoidEta.do
  resume k Tru
  resume k Fls)

delimitFail : {rs : _} -> STM rs String
delimitFail {rs} = AvoidEta.do
  a <- reset0 fail
  pure {rs} ((Cat (Str "Answer was: ") a))

emit : {rs : _} -> Exp a -> STM (List a :: rs) ()
emit a = shift0 (\k => AvoidEta.do
  as <- resume k Uni
  pure ((Con a as)))

collect : {a : _} -> {rs : _} -> STM (List a :: rs) b -> STM rs (List a)
collect {rs} {a} m = reset0 {a=List a} {rs} (
  (>>=) {rs=List a :: rs} m (\u => pure {rs=List a :: rs} Emp))

choice : {rs : _} -> Exp Int -> STM (String :: rs) Int
choice {rs} = letrec {rs = String :: rs} (\recurse => \n => AvoidEta.do
  AvoidEta.ifthenelse {a = Int} ((Sma n (Lit 1)))
    fail
    (AvoidEta.do
      b <- Main.flip
      ifthenelse b
        (pure {rs=String::rs} n)
        (recurse ((Sub n (Lit 1))))))

triple : {rs : _} -> Exp Int -> Exp Int -> STM (String :: rs) (Int, Int, Int)
triple {rs} n s = AvoidEta.do
  i  <- Main.choice {rs} n
  j  <- Main.choice {rs} ((Sub i (Lit 1)))
  k  <- Main.choice {rs} ((Sub j (Lit 1)))
  ifthenelse ((Equ ((Add i ((Add j k)))) s))
    (pure {rs=String::rs} (Tri i j k))
    fail

emitTriples : {rs : _} -> STM (String :: List (Int, Int, Int) :: rs) String
emitTriples {rs} =
  (>>=) {rs=(String :: List (Int, Int, Int) :: rs)} (triple (Lit 9) (Lit 15))  (\ijk =>
  (>>=) {rs=(String :: List (Int, Int, Int) :: rs)} (lift (emit ijk)) (\u =>
  pure {rs=(String :: List (Int, Int, Int) :: rs)} (Str "done")))

emittedTriples : STM [] (List (Int, Int, Int))
emittedTriples = collect {rs=[]} (reset0 (emitTriples {rs=[]}))

first : {rs : _} -> Exp a -> STM (Maybe a :: rs) ()
first {rs} a = shift0 (\k => do
  pure {rs} ((Jus a)))

firstTriples : {rs : _} -> STM (String :: Maybe (Int, Int, Int) :: rs) String
firstTriples {rs} =
  (>>=) {rs=(String :: Maybe (Int, Int, Int) :: rs)} (triple (Lit 9) (Lit 15))  (\ijk =>
  (>>=) {rs=(String :: Maybe (Int, Int, Int) :: rs)} (lift (first ijk)) (\u =>
  pure {rs=(String :: Maybe (Int, Int, Int) :: rs)} (Str "done")))
firstTriple : STM [] (Maybe (Int, Int, Int))
firstTriple = reset0 {a=Maybe (Int,Int,Int)} {rs=[]} (
  (>>=) {rs=[Maybe (Int,Int,Int)]} (reset0 (firstTriples {rs=[]})) (\u =>
  pure {rs=[Maybe (Int,Int,Int)]} Noh))

program : Exp (Stm [String,List Int] String -> Stm [] (List Int))
program = Lam (\m =>
  reify {rs = []} (collect {rs=[]} {a=Int} {b=String} (reset0 {rs=[List Int]} (
    reflect {a=String} {rs=[String,List Int]} m))))

main : IO ()
main = putStrLn (pretty 0 $ runPure emittedTriples)

  -- generated_source : List (Int, Int, Int)
  -- generated_source =
  -- ((((let f0 x1 = (\x2 => (\x3 =>
  --    (if (x1 < 1)
  --      then (x3 "no")
  --      else ((x2 x1) (\x4 => (((f0 (x1 - 1)) x2) x3)))))) in f0) 9) (\x0 => (\x1 =>
  -- ((((let f2 x3 = (\x4 => (\x5 =>
  --    (if (x3 < 1)
  --      then (x5 "no")
  --      else ((x4 x3) (\x6 => (((f2 (x3 - 1)) x4) x5)))))) in f2) (x0 - 1)) (\x2 => (\x3 =>
  -- ((((let f4 x5 = (\x6 => (\x7 =>
  --    (if (x5 < 1)
  --      then (x7 "no")
  --      else ((x6 x5) (\x8 => (((f4 (x5 - 1)) x6) x7)))))) in f4) (x2 - 1)) (\x4 => (\x5 =>
  --        (if ((x0 + (x2 + x4)) == 15)
  --          then ((x0, x2, x4) :: (x5 "done"))
  --          else (x5 "no"))))) x3)))) x1)))) (\x0 => []))
