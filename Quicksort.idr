module Quicksort

%default total

(<=) : Nat -> Nat -> Type
Z <= n        = Unit
(S n) <= Z    = Void
(S n) <= (S m) = n <= m

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

qsort' : (n : Nat) -> (l : List Nat) -> length l <= n -> List Nat
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
