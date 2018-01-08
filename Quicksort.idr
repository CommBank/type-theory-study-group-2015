module Quicksort

%default total

(<=) : Nat -> Nat -> Type
Z <= n        = Unit
(S n) <= Z    = Void
(S n) <= (S m) = n <= m

nlte : Nat -> Nat -> Type
nlte = (<=)

lteSucc : n <= m -> n <= S m
lteSucc {n = Z} {m = m} p = p
lteSucc {n = (S k)} {m = (S j)} p = (lteSucc {n=k} {m=j}) p

lteRefl : n <= n
lteRefl {n = Z} = ()
lteRefl {n = (S k)} = lteRefl {n = k}

lteTrans : i <= j -> j <= k -> i <= k
lteTrans {i=Z} {j=j} _ _ = ()
lteTrans {i=(S i')} {j=(S j')} {k = (S k')} x y = lteTrans {i = i'} {j = j'} {k = k'} x y

filterLemma : length (filter p x) <= length x
filterLemma {x = []} {p = p}        = ()
filterLemma {x = (x :: xs)} {p = p} with (p x)
  filterLemma {x = (x :: xs)} {p = p} | False = lteSucc filterLemma
  filterLemma {x = (x :: xs)} {p = p} | True  = filterLemma

qsort' : .(n : Nat) -> (l : List Nat) -> .(length l <= n) -> List Nat
qsort' n [] p = []
qsort' (S n) (a :: x) p =
  qsort' n (filter (<= a) x) p1
  ++ [a]
  ++ qsort' n (filter (> a) x) p2
  where
    p1 =
      let fl = the (length (filter (<= a) x) <= length x) filterLemma
      in lteTrans {i = length (filter (<= a) x)} {j = length x} {k = n} fl p
    p2 =
      let fl = the (length (filter (> a) x) <= length x) filterLemma
      in lteTrans {i = length (filter (> a) x)} {j = length x} {k = n} fl p

qsort : (l : List Nat) -> List Nat
qsort l = qsort' (length l) l lteRefl

-- naiveQSort : List Nat -> List Nat
-- naiveQSort [] = []
-- naiveQSort (x :: xs) =
--   naiveQSort (filter (<= x) xs)
--   ++ [x]
--   ++ naiveQSort (filter (> x) xs)
main : IO ()
main = putStrLn . show . qsort $ [1,56,3,23,54,23,3,2,1]

sorted : List Nat -> Type
sorted []             = Unit
sorted [a]            = Unit
sorted (x :: y :: xs) = (x <= y, sorted (y :: xs))

occs : Nat -> List Nat -> Nat
occs a []        = 0
occs a (b :: xs) with (a == b)
  occs a (b :: xs) | True  = 1 + occs a xs
  occs a (b :: xs) | False = occs a xs

perm : List Nat -> List Nat -> Nat -> Type
perm l l' a = (occs a l = occs a l')

mem : a -> List a -> Type
mem x []        = Void
mem x (y :: xs) = Either (x = y) (mem x xs)

theorem : {p : length l <= m} -> (sorted (qsort' m l p), (a : Nat) -> perm l (qsort' m l p) a)

subS : S k <= S j = True -> k <= j = True
subS {k = Z} {j = Z}     prf  = Refl
subS {k = Z} {j = S k}   prf  = Refl
subS {k = S k} {j = Z}   Refl impossible
subS {k = S k} {j = S j} prf  = subS {k = S k} {j = S j} ?prf1
  where
    want : S k <= S j = True

infix 6 ~<=
(~<=) : Nat -> Nat -> Bool
(~<=) x y = x < y || x == y

blah : (k : Nat) -> (j : Nat) -> ((S k) ~<= (S j)) = (k ~<= j)

lemma1 : (x ~<= y = True) -> nlte x y
lemma1 {x = Z}   {y = Z}   prf = ()
lemma1 {x = Z}   {y = S k} prf = ()
lemma1 {x = S k} {y = Z}   Refl impossible
lemma1 {x = S k} {y = S j} prf = lemma1 rhs
  where
    rhs : (k < j || k == j) = True
    -- rhs = rewrite blah k j in prf
