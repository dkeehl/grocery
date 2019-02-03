{-
import Pruviloj
import Pruviloj.Induction

%language ElabReflection

isZero : Nat -> Bool
isZero = %runElab (do n <- gensym "n"
                      intro n
                      induction (Var n)
                      compute
                      fill `(True)
                      solve
                      compute
                      attack
                      intros
                      fill `(False)
                      solve
                      solve)
fib : Nat -> Nat
fib n = index n (fibs 0 1)
  where
    fibs : Nat -> Nat -> Stream Nat
    fibs a b = a :: fibs b (a + b)

data Result : Nat -> Type where
  Noop : Result n

getVal : Result n -> Nat
getVal _ {n} = n

test : Result (Main.fib 10)
test = Noop

main : IO ()
main = printLn $ getVal test

-}
import Iaia
import Iaia.Control
import Iaia.Data
import Iaia.Native.Control
import Data.CoList
import Data.Nat.Views

%default total

implementation Recursive (List a) (XNor a) where
  cata alg [] = alg Neither
  cata alg (x::xs) = alg $ Both x (cata alg xs)

implementation Corecursive (CoList a) (XNor a) where
  ana coalg n with (coalg n)
    ana coalg n | Neither = []
    ana coalg n | Both x n' = x :: ana coalg n'
                     
rev : List a -> List a
rev = cata alg where
  alg Neither = []
  alg (Both x xs) = xs ++ [x]

prims : (n: Nat) -> .(2 `LTE` n) -> CoList Nat
prims n _ = sieve [2..n]
  where
    -- Wether n devides m
    notDiv : Nat -> Nat -> Bool
    notDiv Z m = assert_unreachable
    notDiv n@(S _) m = isZero $ modNatNZ m n SIsNotZ

    sieve : List Nat -> CoList Nat
    sieve = ana coalg where
      coalg [] = Neither
      coalg (x::xs) = Both x (filter (notDiv x) xs)

implementation Functor (XNor a) where
  map f Neither = Neither
  map f (Both x y) = Both x (f y)

-- pow itself is total, but due to the partial `hylo`, this implementation has to be
-- partial
partial
pow : Nat -> Nat -> Nat
pow x = hylo alg coalg
  where
    alg : Algebra (XNor Nat) Nat
    alg Neither = 1
    alg (Both x y) = x * y

    coalg : Coalgebra (XNor Nat) Nat
    coalg Z = Neither
    coalg (S k) = Both x k

insert : Ord a => a -> List a -> List a
insert x = cata alg where
  alg Neither = [x]
  alg (Both y ys) = if x < y
                       then x :: y :: ys
                       else y :: x :: ys

insertSort : Ord a => List a -> List a
insertSort = cata alg where
  alg Neither = []
  alg (Both y ys) = insert y ys

bubble : Ord a => List a -> Maybe (a, List a)
bubble = cata alg where
  alg Neither = Nothing
  alg (Both x Nothing) = Just (x, [])
  alg (Both x (Just (y, ys))) = if x < y
                                   then Just (x, y::ys)
                                   else Just (y, x::ys)

bubbleSort : Ord a => List a -> CoList a
bubbleSort xs = ana coalg (bubble xs) where
  coalg Nothing = Neither 
  coalg (Just (y, ys)) = Both y (bubble ys)

data LeafTreeF : Type -> Type -> Type where
  LeafF : a -> LeafTreeF a b
  SplitF : b -> b -> LeafTreeF a b

implementation Functor (LeafTreeF a) where
  map f (LeafF x) = LeafF x
  map f (SplitF l r) = SplitF (f l) (f r)

treeProd : Algebra (LeafTreeF Nat) Nat
treeProd (LeafF n) = n
treeProd (SplitF n m) = n * m

partial
fac : Nat -> Nat
fac n = hylo treeProd coalg (1, n)
  where
    coalg : Coalgebra (LeafTreeF Nat) (Nat, Nat)
    -- m is the minimal nat in the subtree, and n is the number of nats in the
    -- subtree
    coalg (m, Z) = LeafF m
    coalg (m, S Z) = LeafF m
    coalg (m, n) = let n' = divNatNZ n 2 SIsNotZ in
                       SplitF (m, n') (m + n', minus n n')

partial
pow' : Nat -> Nat -> Nat
pow' x = hylo treeProd coalg
  where
    coalg : Coalgebra (LeafTreeF Nat) Nat
    coalg Z = LeafF 1
    coalg (S Z) = LeafF x
    coalg k with (half k)
      coalg (S (n + n)) | HalfOdd = SplitF n (S n)
      coalg (n + n) | HalfEven = SplitF n n

split : List a -> (List a, List a)
split = cata alg where
  alg Neither = ([], [])
  alg (Both x (l, l')) = (l', x :: l)

partial
mergeSort : Ord a => List a -> List a
mergeSort = hylo alg coalg
  where
    alg : Algebra (LeafTreeF (List a)) (List a)
    alg (LeafF l) = l
    alg (SplitF l r) = merge l r

    coalg : Coalgebra (LeafTreeF (List a)) (List a)
    coalg [] = LeafF []
    coalg [x] = LeafF [x]
    coalg xs = let (l, r) = split xs in SplitF l r

partial
main : IO ()
main = printLn $ fac 10
