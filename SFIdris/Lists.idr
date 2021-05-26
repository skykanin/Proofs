module Lists

import Basics

import Data.Nat as N

%hide Prelude.count
%hide Prelude.List.(++)
%hide Prelude.List.length
%hide Prelude.Strings.length

%default total

public export
data NatProd : Type where
  Pair : Nat -> Nat -> NatProd

public export
fst : NatProd -> Nat
fst (Pair x y) = x

public export
snd : NatProd -> Nat
snd (Pair x y) = y

public export
fst' : NatProd -> Nat
fst' (Pair x _) = x

public export
snd' : NatProd -> Nat
snd' (Pair _ y) = y

public export
swap_pair : NatProd -> NatProd
swap_pair (Pair x y) = (Pair y x)

-- If we state things in a peculiar way, we can complete the proof with reflexivity
public export
surjective_pairing' : (n, m : Nat) -> (n, m) = (fst (n, m), snd (n, m))
surjective_pairing' n m = Refl

-- If we state it in a more natural way we have to expose the structure of p
public export
surjective_pairing : (p : NatProd) -> p = Pair (fst p) (snd p)
surjective_pairing p = case p of (Pair n m) => Refl

public export
snd_fst_is_swap : (p : NatProd) -> Pair (snd p) (fst p) = swap_pair p
snd_fst_is_swap (Pair x y) = Refl

public export
fst_swap_is_snd : (p : NatProd) -> fst (swap_pair p) = snd p
fst_swap_is_snd (Pair x y) = Refl

public export
data NatList : Type where
  Nil : NatList
  (::) : Nat -> NatList -> NatList
  
public export
repeat : (n, count : Nat) -> NatList
repeat n Z = []
repeat n (S k) = n :: repeat n k

public export
length : NatList -> Nat
length [] = Z
length (h :: t) = S (length t)

public export
app : (l1, l2 : NatList) -> NatList
app [] l2 = l2
app (h :: t) l2 = h :: app t l2

infixr 7 ++
(++) : (x, y : NatList) -> NatList
(++) = app

public export
hd : (d : Nat) -> (l : NatList) -> Nat
hd d [] = d
hd _ (h :: _) = h

public export
tl : (l : NatList) -> NatList
tl [] = []
tl (_ :: t) = t

public export
nonzeros : (l : NatList) -> NatList
nonzeros [] = []
nonzeros (Z :: t) = nonzeros t
nonzeros (h :: t) = h :: nonzeros t

test_nonzeros : nonzeros [0,1,0,2,3,0,0] = [1,2,3]
test_nonzeros = Refl

public export
oddmembers : (l : NatList) -> NatList
oddmembers [] = []
oddmembers (h :: t) = if evenb h then oddmembers t else h :: oddmembers t

test_oddmembers : oddmembers [0,1,0,2,3,0,0] = [1,3]
test_oddmembers = Refl

public export
countoddmembers : (l : NatList) -> Nat
countoddmembers [] = Z
countoddmembers (h :: t) =
  if oddb h
  then S (countoddmembers t)
  else countoddmembers t

test_countoddmembers : countoddmembers [1,0,3,1,4,5] = 4
test_countoddmembers = Refl

public export
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

public export
Bag : Type
Bag = NatList

public export
count : (v : Nat) -> (s : Bag) -> Nat
count _ [] = Z
count v (h :: t) = if beq_nat h v then S (count v t) else count v t

test_count1 : count 1 [1,2,3,1,4,1] = 3
test_count1 = Refl

test_count2 : count 6 [1,2,3,1,4,1] = 0
test_count2 = Refl

public export
sum : Bag -> Bag -> Bag
sum = (++)

test_sum1 : count 1 (sum [1,2,3] [1,4,1]) = 3
test_sum1 = Refl

public export
add : (v : Nat) -> (s : Bag) -> Bag
add v s = v :: s

test_add1 : count 1 (add 1 [1,3,1]) = 3
test_add1 = Refl

test_add2 : count 5 (add 1 [1,4,1]) = 0
test_add2 = Refl

public export
member : (v : Nat) -> (s : Bag) -> Bool
member _ [] = False
member v (h :: t) = if h == v then True else member v t

test_member1 : member 1 [1,4,1] = True
test_member1 = Refl

test_member2 : member 2 [1,4,1] = False
test_member2 = Refl

public export
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

public export
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

public export
subset : (s1: Bag) -> (s2 : Bag) -> Bool
subset [] _ = True
subset _ [] = False
subset (h1 :: t1) s2 = if member h1 s2 then subset t1 (remove_one h1 s2) else False

test_subset1 : subset [1,2] [2,1,4,1] = True
test_subset1 = Refl

test_subset2 : subset [1,2,2] [2,1,4,1] = False
test_subset2 = Refl

public export
nil_app : (l : NatList) -> ([] ++ l) = l
nil_app l = Refl

public export
tl_length_pred : (l : NatList) -> Basics.Numbers.pred (length l) = length (tl l)
tl_length_pred [] = Refl
tl_length_pred (h :: t) = Refl

public export
app_assoc : (l1, l2, l3 : NatList) -> (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
app_assoc [] l2 l3 = Refl
app_assoc (h :: t) l2 l3 =
  let inductiveHypothesis = app_assoc t l2 l3 in
  rewrite inductiveHypothesis in Refl
  
public export
rev : (l : NatList) -> NatList  
rev [] = []
rev (h :: t) = (rev t) ++ [h]

public export
app_length : (l1, l2 : NatList) -> length (l1 ++ l2) = (length l1) + (length l2)
app_length [] l2 = Refl
app_length (h :: t) l2 = rewrite app_length t l2 in Refl

public export
rev_length : (l : NatList) -> length (rev l) = length l
rev_length [] = Refl
rev_length (n :: l') =
  rewrite app_length (rev l') [n] in
  rewrite plusCommutative (length (rev l')) 1 in
  let inductiveHypothesis = rev_length l' in
    rewrite inductiveHypothesis in Refl

public export
nil_app_r : (l : NatList) -> (l ++ []) = l
nil_app_r [] = Refl
nil_app_r (n :: l') = rewrite nil_app_r l' in Refl

public export
rev_app_distr : (l1, l2 : NatList) -> rev (l1 ++ l2) = (rev l2) ++ (rev l1)
rev_app_distr [] l2 = rewrite nil_app_r (rev l2) in Refl
rev_app_distr (n :: l1') l2 =
  rewrite rev_app_distr l1' l2 in
  rewrite app_assoc (rev l2) (rev l1') [n] in Refl
  
public export
rev_involutive : (l : NatList) -> rev (rev l) = l
rev_involutive [] = Refl
rev_involutive (n :: l') =
  rewrite rev_app_distr (rev l') [n] in
  rewrite rev_involutive l' in Refl

public export
app_assoc4 : (l1, l2, l3, l4 : NatList) ->
             l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4
app_assoc4 l1 l2 l3 l4 =
  rewrite app_assoc (l1 ++ l2) l3 l4 in
  rewrite sym (app_assoc l1 l2 (l3 ++ l4)) in Refl

public export
nonzeros_app : (l1, l2 : NatList) ->
               nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
nonzeros_app [] l2 = Refl
nonzeros_app (n :: l1') l2 =
  let iH = nonzeros_app l1' l2 in
  case n of
    Z => rewrite iH in Refl
    (S k) => rewrite iH in Refl

public export
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

public export
beq_NatList_refl : (l : NatList) -> True = beq_NatList l l
beq_NatList_refl [] = Refl
beq_NatList_refl (n :: l') =
  rewrite sym (beq_nat_refl n) in
  rewrite beq_NatList_refl l' in Refl

public export
count_member_nonzero : (s : Bag) -> lte 1 (count 1 (1 :: s)) = True
count_member_nonzero [] = Refl
count_member_nonzero (n :: s') = Refl

public export
ble_n_Sn : (n : Nat) -> lte n (S n) = True
ble_n_Sn Z = Refl
ble_n_Sn (S k) = rewrite ble_n_Sn k in Refl

public export
remove_decreases_count : (s : Bag) ->
                         lte (count 0 (remove_one 0 s)) (count 0 s) = True
remove_decreases_count [] = Refl
remove_decreases_count (Z :: s') =
  rewrite ble_n_Sn (count Z s') in Refl
remove_decreases_count ((S k) :: s') =
  let iH = remove_decreases_count s' in
  rewrite iH in Refl
  
public export
rev_twice : {l1, l2 : NatList} -> rev (rev l1) = rev (rev l2) -> l1 = l2
rev_twice {l1} {l2} prf =
  let a = rev_involutive l1
      b = rev_involutive l2 in
  replace {p = \x => l1 = x} b `apply` replace {p = \x => x = rev (rev l2)} a prf

public export
rev_injective' : (l1, l2 : NatList) -> rev l1 = rev l2 -> l1 = l2
rev_injective' l1 l2 prf =
  let p = cong rev prf in
  rev_twice {l1 = l1} {l2 = l2} p
  
public export
rev_injective : (l1, l2 : NatList) -> rev l1 = rev l2 -> l1 = l2
rev_injective l1 l2 prf =
  rewrite sym (rev_involutive l1) in
  rewrite prf in
  rev_involutive l2

public export
data NatOption : Type where
  Some : Nat -> NatOption
  None : NatOption

public export
option_elim : (d : Nat) -> (o : NatOption) -> Nat
option_elim _ (Some k) = k
option_elim d None = d

hd_error : (l : NatList) -> NatOption
hd_error [] = None
hd_error (x :: _) = Some x

test_hd_error1 : hd_error [] = None
test_hd_error1 = Refl

test_hd_error2 : hd_error [1] = Some 1
test_hd_error2 = Refl

test_hd_error3 : hd_error [5, 6] = Some 5
test_hd_error3 = Refl

public export
option_elim_hd : (l : NatList) -> (d : Nat) -> hd d l = option_elim d (hd_error l)
option_elim_hd [] _ = Refl
option_elim_hd (x :: _) _ = Refl

public export
data Id : Type where
  MkId : Nat -> Id

public export
beq_id : (x1, x2 : Id) -> Bool
beq_id (MkId n1) (MkId n2) = n1 == n2

public export
beq_id_refl : (x : Id) -> True = beq_id x x
beq_id_refl (MkId n) = rewrite sym (eq_nat_refl n) in Refl

namespace PartialMap

  public export
  data PartialMap : Type where
    Empty : PartialMap
    Record : Id -> Nat -> PartialMap -> PartialMap

  public export
  update : (d : PartialMap) -> (x : Id) -> (value : Nat) -> PartialMap
  update d x value = Record x value d

  public export
  find : (x : Id) -> (d : PartialMap) -> NatOption
  find _ Empty = None
  find x (Record y v d') =
    if beq_id x y
    then Some v
    else find x d'

  -- ||| An updated record will never yield an empty record
  public export
  never_empty : (d : PartialMap) -> (x : Id) -> (v : Nat) -> update d x v = Record x v d
  never_empty d x v = Refl

  public export
  update_eq : (d : PartialMap) -> (x : Id) -> (v : Nat) -> find x (update d x v) = Some v
  update_eq d x v =
    let is_rec = never_empty d x v
        is_eq = beq_id_refl x
    in replace {p = \r => find x r = Some v} is_rec (rewrite sym is_eq in Refl)

  public export
  update_neq : (d : PartialMap) -> (x, y: Id) -> (o : Nat) -> beq_id x y = False -> find x (update d y o) = find x d
  update_neq d x y o prf =
    let is_rec = never_empty d y o
    in replace {p = \r => find x r = find x d} is_rec (rewrite prf in Refl)
