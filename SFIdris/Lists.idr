module Lists

import Basics

%hide Prelude.Basics.fst
%hide Prelude.Basics.snd
%hide Prelude.Nat.pred
%hide Prelude.pred
%hide Prelude.List.(++)
%hide Prelude.List.length
%hide Prelude.Strings.length

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
nonzeros (Z :: t) = nonzeros t
nonzeros (h :: t) = h :: nonzeros t

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
count v (h :: t) = if beq_nat h v then S (count v t) else count v t

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
  case beq_nat h v of
    True => t
    False =>  h :: remove_one v t

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
  if beq_nat h v then remove_all v t else h :: remove_all v t

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

nil_app : (l : NatList) -> ([] ++ l) = l
nil_app l = Refl

tl_length_pred : (l : NatList) -> pred (length l) = length (tl l)
tl_length_pred [] = Refl
tl_length_pred (h :: t) = Refl

app_assoc : (l1, l2, l3 : NatList) -> (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
app_assoc [] l2 l3 = Refl
app_assoc (h :: t) l2 l3 =
  let inductiveHypothesis = app_assoc t l2 l3 in
  rewrite inductiveHypothesis in Refl
  
rev : (l : NatList) -> NatList  
rev [] = []
rev (h :: t) = (rev t) ++ [h]

app_length : (l1, l2 : NatList) -> length (l1 ++ l2) = (length l1) + (length l2)
app_length [] l2 = Refl
app_length (h :: t) l2 = rewrite app_length t l2 in Refl

rev_length : (l : NatList) -> length (rev l) = length l
rev_length [] = Refl
rev_length (n :: l') =
  rewrite app_length (rev l') [n] in
  rewrite plusCommutative (length (rev l')) 1 in
  let inductiveHypothesis = rev_length l' in
    rewrite inductiveHypothesis in Refl

nil_app_r : (l : NatList) -> (l ++ []) = l
nil_app_r [] = Refl
nil_app_r (n :: l') = rewrite nil_app_r l' in Refl

rev_app_distr : (l1, l2 : NatList) -> rev (l1 ++ l2) = (rev l2) ++ (rev l1)
rev_app_distr [] l2 = rewrite nil_app_r (rev l2) in Refl
rev_app_distr (n :: l1') l2 =
  rewrite rev_app_distr l1' l2 in
  rewrite app_assoc (rev l2) (rev l1') [n] in Refl
  
rev_involutive : (l : NatList) -> rev (rev l) = l
rev_involutive [] = Refl
rev_involutive (n :: l') =
  rewrite rev_app_distr (rev l') [n] in
  rewrite rev_involutive l' in Refl

app_assoc4 : (l1, l2, l3, l4 : NatList) ->
             l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4
app_assoc4 l1 l2 l3 l4 =
  rewrite app_assoc (l1 ++ l2) l3 l4 in
  rewrite sym (app_assoc l1 l2 (l3 ++ l4)) in Refl

nonzeros_app : (l1, l2 : NatList) ->
               nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
nonzeros_app [] l2 = Refl
nonzeros_app (n :: l1') l2 =
  let iH = nonzeros_app l1' l2 in
  case n of
    Z => rewrite iH in Refl
    (S k) => rewrite iH in Refl

beq_NatList : (l1, l2 : NatList) -> Bool
beq_NatList [] [] = True
beq_NatList [] _  = False
beq_NatList _ []  = False
beq_NatList (h1 :: t1) (h2 :: t2) =
  if beq_nat h1 h2 then beq_NatList t1 t2 else False

test_beq_NatList1 : beq_NatList Nil Nil = True
test_beq_NatList1 = Refl

test_beq_NatList2 : beq_NatList [1,2,3] [1,2,3] = True
test_beq_NatList2 = Refl

test_beq_NatList3 : beq_NatList [1,2,3] [1,2,4] = False
test_beq_NatList3 = Refl

beq_NatList_refl : (l : NatList) -> True = beq_NatList l l
beq_NatList_refl [] = Refl
beq_NatList_refl (n :: l') =
  rewrite sym (beq_nat_refl n) in
  rewrite beq_NatList_refl l' in Refl

count_member_nonzero : (s : Bag) -> lte 1 (count 1 (1 :: s)) = True
count_member_nonzero [] = Refl
count_member_nonzero (n :: s') = Refl

ble_n_Sn : (n : Nat) -> lte n (S n) = True
ble_n_Sn Z = Refl
ble_n_Sn (S k) = rewrite ble_n_Sn k in Refl

remove_decreases_count : (s : Bag) ->
                         lte (count 0 (remove_one 0 s)) (count 0 s) = True
remove_decreases_count [] = Refl
remove_decreases_count (Z :: s') =
  rewrite ble_n_Sn (count Z s') in Refl
remove_decreases_count ((S k) :: s') =
  let iH = remove_decreases_count s' in
  rewrite iH in Refl
  
rev_twice : {l1, l2 : NatList} -> rev (rev l1) = rev (rev l2) -> l1 = l2
rev_twice {l1} {l2} prf =
  let a = rev_involutive l1
      b = rev_involutive l2 in
  replace b {P = \x => l1 = x} `apply` replace a {P = \x => x = rev (rev l2)} prf

rev_injective' : (l1, l2 : NatList) -> rev l1 = rev l2 -> l1 = l2
rev_injective' l1 l2 prf =
  let p = cong prf {f = rev} in
  rev_twice {l1 = l1} {l2 = l2} p
  
rev_injective : (l1, l2 : NatList) -> rev l1 = rev l2 -> l1 = l2
rev_injective l1 l2 prf =
  rewrite sym (rev_involutive l1) in
  rewrite prf in
  rev_involutive l2
