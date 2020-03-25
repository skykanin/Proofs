module Lists

import Basics

%hide Prelude.Basics.fst
%hide Prelude.Basics.snd
%hide Prelude.Nat.pred
%hide Prelude.List.(++)

%access public export
%default total

data NatProd : Type where
  Pair : Nat -> Nat -> NatProd

fst : NatProd -> Nat
fst (Pair x y) = x

snd : NatProd -> Nat
snd (Pair x y) = y

syntax "(" [x] "," [y] ")" = Pair x y

fst' : NatProd -> Nat
fst' (x, y) = x

snd' : NatProd -> Nat
snd' (x, y) = y

swap_pair : NatProd -> NatProd
swap_pair (x, y) = (y, x)

-- If we state things in a peculiar way, we can complete the proof with reflexivity
surjective_pairing' : (n, m : Nat) -> (n, m) = (fst (n, m), snd (n, m))
surjective_pairing' n m = Refl

-- If we state it in a more natural way we have to expose the structure of p
surjective_pairing : (p : NatProd) -> p = (fst p, snd p)
surjective_pairing p = case p of (n, m) => Refl

snd_fst_is_swap : (p : NatProd) -> (snd p, fst p) = swap_pair p
snd_fst_is_swap (x, y) = Refl

fst_swap_is_snd : (p : NatProd) -> fst (swap_pair p) = snd p
fst_swap_is_snd (x, y) = Refl

data NatList : Type where
  Nil : NatList
  (::) : Nat -> NatList -> NatList
  
repeat : (n, count : Nat) -> NatList
repeat n Z = []
repeat n (S k) = n :: repeat n k

length : NatList -> Nat
length [] = Z
length (h :: t) = S (length t)

app : (l1, l2 : NatList) -> NatList
app [] l2 = l2
app (h :: t) l2 = h :: app t l2

infixr 7 ++
(++) : (x, y : NatList) -> NatList
(++) = app

hd : (default : Nat) -> (l : NatList) -> Nat
hd default [] = default
hd _ (h :: _) = h

tl : (l : NatList) -> NatList
tl [] = []
tl (_ :: t) = t

nonzeros : (l : NatList) -> NatList
nonzeros [] = []
nonzeros (h :: t) = if h == 0 then nonzeros t else h :: nonzeros t

test_nonzeros : nonzeros [0,1,0,2,3,0,0] = [1,2,3]
test_nonzeros = Refl

oddmembers : (l : NatList) -> NatList
oddmembers [] = []
oddmembers (h :: t) = if evenb h then oddmembers t else h :: oddmembers t

test_oddmembers : oddmembers [0,1,0,2,3,0,0] = [1,3]
test_oddmembers = Refl

countoddmembers : (l : NatList) -> Nat
countoddmembers [] = 0
countoddmembers (h :: t) =
  if evenb h
  then countoddmembers t
  else 1 + countoddmembers t

test_countoddmembers : countoddmembers [1,0,3,1,4,5] = 4
test_countoddmembers = Refl

alternate : (l1, l2 : NatList) -> NatList
alternate [] l2 = l2
alternate l1 [] = l1
alternate (h1 :: t1) (h2 :: t2) = h1 :: h2 :: alternate t1 t2

test_alternate1 : alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6]
test_alternate1 = Refl

test_alternate2 : alternate [1] [4,5,6] = [1,4,5,6]
test_alternate2 = Refl

test_alternate3 : alternate [1,2,3] [4] = [1,4,2,3]
test_alternate3 = Refl

test_alternate4 : alternate [] [20,30] = [20,30]
test_alternate4 = Refl
