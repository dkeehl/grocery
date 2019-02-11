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
    notDiv n@(S _) m = isSucc $ modNatNZ m n SIsNotZ

    sieve : List Nat -> CoList Nat
    sieve = ana coalg where
      coalg [] = Neither
      coalg (x::xs) = Both x (filter (notDiv x) xs)

implementation Functor (XNor a) where
  map f Neither = Neither
  map f (Both x y) = Both x (f y)

-- Note that `hylo` is partial, so all implementations using it are partial
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
    -- m is the minimal nat in the subtree, and n is the number of nats in the subtree
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

data BinTreeF : Type -> Type -> Type where
  TipF : BinTreeF _ _
  BranchF : a -> b -> b -> BinTreeF a b

implementation Functor (BinTreeF a) where
  map f TipF = TipF
  map f (BranchF x y z) = BranchF x (f y) (f z)

binTreeProd : Algebra (BinTreeF Nat) Nat
binTreeProd TipF = 1
binTreeProd (BranchF x y z) = x * y * z

partial
pac' : Nat -> Nat
pac' n = hylo binTreeProd coalg 1
  where
    coalg : Coalgebra (BinTreeF Nat) Nat
    coalg Z = TipF
    coalg x with (compare (x * 2) n)
      | EQ = BranchF x (x * 2) 0
      | LT = BranchF x (x * 2) (x * 2 + 1)
      | GT = BranchF x 0 0

partial
pow'' : Nat -> Nat -> Nat
pow'' x = hylo binTreeProd coalg
  where
    coalg : Coalgebra (BinTreeF Nat) Nat
    coalg Z = TipF
    coalg (S Z) = BranchF x 0 0
    coalg n = let half = divNatNZ n 2 SIsNotZ in
                  BranchF x half (minus n half)

partition : List a -> (a -> Bool) -> (List a, List a)
partition xs f = cata alg xs where
  alg Neither = ([], [])
  alg (Both x (l, r)) = if f x
                           then (x::l, r)
                           else (l, x::r)

partial
quickSort : Ord a => List a -> List a
quickSort = hylo alg coalg
  where
    alg : Algebra (BinTreeF a) (List a)
    alg TipF = []
    alg (BranchF x l r) = l ++ (x::r)

    coalg : Ord a => Coalgebra (BinTreeF a) (List a)
    coalg [] = TipF
    coalg (x::xs) = let (l, r) = partition xs (< x) in
                        BranchF x l r

codata CoBinTree : Type -> Type where
  Tip : CoBinTree a 
  Branch : a -> CoBinTree a -> CoBinTree a -> CoBinTree a

implementation Corecursive (CoBinTree a) (BinTreeF a) where
  ana coalg t with (coalg t)
    | TipF = Tip
    | (BranchF x l r) = Branch x (ana coalg l) (ana coalg r)

combine : Ord a => CoBinTree a -> CoBinTree a -> CoBinTree a
combine t Tip = t
combine Tip t = t
combine t@(Branch x l r) t'@(Branch y l' r')
  = if x < y
       then Branch x l (combine r t')
       else Branch y (combine t l') r

heapToList : Ord a => CoBinTree a -> CoList a
heapToList = ana coalg where
  coalg Tip = Neither
  coalg (Branch x l r) = Both x (combine l r)

decompose : Ord a => List a -> Maybe (a, List a, List a)
decompose l = do (x, xs) <- bubble l
                 let (l, r) = partition xs (< x)
                 pure (x, l, r)

listToHeap : Ord a => List a -> CoBinTree a
listToHeap = ana coalg
  where
    coalg : Coalgebra (BinTreeF a) (List a)
    coalg xs with (decompose xs)
      | Nothing = TipF
      | Just (x, l, r) = BranchF x l r

heapSort : Ord a => List a -> CoList a
heapSort = heapToList . listToHeap
