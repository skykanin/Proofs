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
countoddmembers [] = Z
countoddmembers (h :: t) =
  if oddb h
  then S (countoddmembers t)
  else countoddmembers t

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

Bag : Type
Bag = NatList

count : (v : Nat) -> (s : Bag) -> Nat
count _ [] = Z
count v (h :: t) = if h == v then S (count v t) else count v t

test_count1 : count 1 [1,2,3,1,4,1] = 3
test_count1 = Refl

test_count2 : count 6 [1,2,3,1,4,1] = 0
test_count2 = Refl

sum : Bag -> Bag -> Bag
sum = (++)

test_sum1 : count 1 (sum [1,2,3] [1,4,1]) = 3
test_sum1 = Refl

add : (v : Nat) -> (s : Bag) -> Bag
add v s = v :: s

test_add1 : count 1 (add 1 [1,3,1]) = 3
test_add1 = Refl

test_add2 : count 5 (add 1 [1,4,1]) = 0
test_add2 = Refl

member : (v : Nat) -> (s : Bag) -> Bool
member _ [] = False
member v (h :: t) = if h == v then True else member v t

test_member1 : member 1 [1,4,1] = True
test_member1 = Refl

test_member2 : member 2 [1,4,1] = False
test_member2 = Refl

remove_one : (v : Nat) -> (s : Bag) -> Bag
remove_one _ [] = []
remove_one v l@(h :: t) =
  if member v l
  then if h == v then t else h :: remove_one v t
  else l

test_remove_one1 : count 5 (remove_one 5 [2,1,5,4,1]) = 0
test_remove_one1 = Refl

test_remove_one2 : count 5 (remove_one 5 [2,1,4,1]) = 0
test_remove_one2 = Refl

test_remove_one3 : count 4 (remove_one 5 [2,1,5,4,1,4]) = 2
test_remove_one3 = Refl

test_remove_one4 : count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1
test_remove_one4 = Refl

remove_all : (v : Nat) -> (s : Bag) -> Bag
remove_all v [] = []
remove_all v l@(h :: t) =
  if member v l
  then if h == v then remove_all v t else h :: remove_all v t
  else l

test_remove_all1 : count 5 (remove_all 5 [2,1,5,4,1]) = 0
test_remove_all1 = Refl

test_remove_all2 : count 5 (remove_all 5 [2,1,4,1]) = 0
test_remove_all2 = Refl

test_remove_all3 : count 4 (remove_all 5 [2,1,5,4,1,4]) = 2
test_remove_all3 = Refl

test_remove_all4 : count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0
test_remove_all4 = Refl

subset : (s1: Bag) -> (s2 : Bag) -> Bool
subset [] _ = True
subset _ [] = False
subset (h1 :: t1) s2 = if member h1 s2 then subset t1 (remove_one h1 s2) else False

test_subset1 : subset [1,2] [2,1,4,1] = True
test_subset1 = Refl

test_subset2 : subset [1,2,2] [2,1,4,1] = False
test_subset2 = Refl
