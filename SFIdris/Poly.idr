module Poly

import Basics

import Data.List
import Data.Nat

%hide Prelude.Strings.(++)
%hide Prelude.List.length
%hide Data.List.filter
%hide Data.List.partition
%hide Prelude.map
%hide Data.Nat.pred
%hide Basics.Playground2.plus

%default total

repeat : (x_ty : Type) -> (x : x_ty) -> (count : Nat) -> List x_ty
repeat x_ty x Z = Nil
repeat x_ty x (S count') = x :: repeat x_ty x count'

repeat' : {x_ty : Type} -> (x : x_ty) -> (count : Nat) -> List x_ty
repeat' x Z = Nil
repeat' x (S count') = x :: repeat' x count'

repeat'' : (x : x_ty) -> (count : Nat) -> List x_ty
repeat'' x Z = Nil
repeat'' x (S count') = x :: repeat'' x count'

public export
app : (l1, l2 : List x) -> List x
app [] l2 = l2
app (h :: t) l2 = h :: app t l2

public export
rev : (l : List x) -> List x
rev [] = []
rev (h :: t) = (rev t) ++ [h]

public export
length : (l : List x) -> Nat
length [] = Z
length (_::l') = S (length l')

test_rev1 : rev [1, 2] = [2, 1]
test_rev1 = Refl

test_rev2 : rev [True] = [True]
test_rev2 = Refl

test_length1 : length [1, 2, 3] = 3
test_length1 = Refl

public export
app_nil_r : (l : List x) -> l ++ [] = l
app_nil_r [] = Refl
app_nil_r (x :: xs) = rewrite app_nil_r xs in Refl

public export
app_assoc : (l, m, n : List a) -> l ++ (m ++ n) = (l ++ m) ++ n
app_assoc [] m n = Refl
app_assoc (x :: xs) m n = rewrite app_assoc xs m n in Refl

public export
app_length : (l1, l2 : List x) -> length (l1 ++ l2) = length l1 + length l2
app_length [] l2 = Refl
app_length (x :: xs) l2 =
  rewrite app_length xs l2 in Refl

public export
rev_app_distr : (l1, l2 : List x) -> rev (l1 ++ l2) = rev l2 ++ rev l1
rev_app_distr [] l2 = rewrite app_nil_r (rev l2) in Refl
rev_app_distr (x :: xs) l2 =
  let iH = rev_app_distr xs l2
      assoc = app_assoc (rev l2) (rev xs) [x]
  in rewrite iH in rewrite sym assoc in Refl

public export
rev_involutive : (l : List x) -> rev (rev l) = l
rev_involutive [] = Refl
rev_involutive (x :: xs) =
  let iH = rev_involutive xs
      dist = rev_app_distr (rev xs) [x]
  in rewrite dist in rewrite iH in Refl

public export
data Prod : (x, y : Type) -> Type where
  PPair : x -> y -> Prod x y

public export
fst : (p : Prod x y) -> x
fst (PPair x _) = x

public export
snd : (p : Prod x y) -> y
snd (PPair _ y) = y

public export
zip : (lx : List x) -> (ly : List y) -> List (Prod x y)
zip [] _ = []
zip _ [] = []
zip (x :: xs) (y :: ys) = PPair x y :: zip xs ys

split : (l : List (Prod x y)) -> Prod (List x) (List y)
split l = PPair (fsts l) (snds l)
  where
    fsts : List (Prod x y) -> List x
    fsts [] = []
    fsts (h :: t) = fst h :: fsts t
    snds : List (Prod x y) -> List y
    snds [] = []
    snds (h :: t) = snd h :: snds t

test_split : split [PPair 1 False, PPair 2 False] = PPair [1, 2] [False, False]
test_split = Refl

data Option : (x : Type) -> Type where
  Some : x -> Option x
  None : Option x

nth_error : (l : List x) -> (n : Nat) -> Option x
nth_error [] n = None
nth_error (a :: l') n = if n == 0 then Some a else nth_error l' (pred n)

test_nth_error1 : nth_error [4,5,6,7] 0 = Some 4
test_nth_error1 = Refl

test_nth_error2 : nth_error [[1], [2]] 1 = Some [2]
test_nth_error2 = Refl

test_nth_error3 : nth_error [True] 2 = None
test_nth_error3 = Refl

hd_error : (l : List x) -> Option x
hd_error [] = None
hd_error (x :: _) = Some x

test_hd_error1 : hd_error [1,2] = Some 1
test_hd_error1 = Refl

test_hd_error2 : hd_error [[1], [2]] = Some [1]
test_hd_error2 = Refl

doit3times : (f : x -> x) -> (n : x) -> x
doit3times f n = f (f (f n))

test_doit3times : doit3times Numbers.minusTwo 9 = 3
test_doit3times = Refl

test_doit3times' : doit3times Prelude.not True = False
test_doit3times' = Refl

filter : (predicate : x -> Bool) -> (l : List x) -> List x
filter predicate [] = []
filter predicate (h :: t) =
  if predicate h
  then h :: filter predicate t
  else filter predicate t

test_filter1 : filter Numbers.evenb [1,2,3,4] = [2,4]
test_filter1 = Refl

length_is_1 : (l : List x) -> Bool
length_is_1 l = length l == 1

test_filter2 : filter Poly.length_is_1 [[1,2], [3], [4], [5,6,7], [], [8]] = [[3], [4], [8]]
test_filter2 = Refl

countoddmembers' : (l : List Nat) -> Nat
countoddmembers' l = length (filter Numbers.oddb l)

test_countoddmembers'1 : countoddmembers' [1,0,3,1,4,5] = 4
test_countoddmembers'1 = Refl

test_countoddmembers'2 : countoddmembers' [0, 2, 4] = 0
test_countoddmembers'2 = Refl

test_countoddmembers'3 : countoddmembers' [] = 0
test_countoddmembers'3 = Refl

test_anon_fun' : doit3times (\n => n * n) 2 = 256
test_anon_fun' = Refl

test_filter2' : filter (\l => length l == 1) [[1,2], [3], [4], [5,6,7], [], [8]] = [[3], [4], [8]]
test_filter2' = Refl

filter_even_gt7 : (l : List Nat) -> List Nat
filter_even_gt7 = filter (\n => n > 7 && evenb n)

test_filter_even_gt7_1 : filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8]
test_filter_even_gt7_1 = Refl

test_filter_even_gt7_2 : filter_even_gt7 [5,2,6,19,129] = []
test_filter_even_gt7_2 = Refl

partition : (f : x -> Bool) -> (l : List x) -> Prod (List x) (List x)
partition f xs = PPair (filter f xs) (filter (Prelude.not . f) xs)

test_parition1 : partition Numbers.oddb [1,2,3,4,5] = PPair [1,3,5] [2,4]
test_parition1 = Refl

test_parition2 : partition (\_ => False) [5,9,0] = PPair [] [5,9,0]
test_parition2 = Refl

map : (f : x -> y) -> (l : List x) -> List y
map _ [] = []
map f (x :: xs) = f x :: map f xs

test_map1 : map (\x => 3 + x) [2,0,2] = [5,3,5]
test_map1 = Refl

test_map2 : map Numbers.oddb [2,1,2,5] = [False, True, False, True]
test_map2 = Refl

test_map3 : map (\n => [evenb n, oddb n]) [2,1,2,5] = [[True, False], [False, True], [True, False], [False, True]]
test_map3 = Refl

map_app_distr : (f : x -> y) -> (a, b : List x) -> map f (a ++ b) = map f a ++ map f b
map_app_distr f [] b = Refl
map_app_distr f (x :: xs) b =
  rewrite map_app_distr f xs b in Refl

map_rev : (f : x -> y) -> (l : List x) -> map f (rev l) = rev (map f l)
map_rev f [] = Refl
map_rev f (x :: xs) =
  let iH = map_rev f xs
  in rewrite sym iH
  in map_app_distr f (rev xs) [x]

flat_map : (f : x -> List y) -> (l : List x) -> List y
flat_map f l = concat (map f l)

test_flat_map1 : flat_map (\n => [n,n,n]) [1,5,4] = [1,1,1,5,5,5,4,4,4]
test_flat_map1 = Refl

option_map : (f : x -> y) -> (xo : Option x) -> Option y
option_map _ None = None
option_map f (Some x) = Some (f x)

fold : (f : x -> y -> y) -> (l : List x) -> (b : y) -> y
fold _ [] b = b
fold f (x :: xs) b = f x (fold f xs b)

fold_example1 : fold (*) [1,2,3,4] 1 = 24
fold_example1 = Refl

fold_example2 : fold Booleans.andb [True, True, False, True] True = False
fold_example2 = Refl

fold_example3 : fold (++) [[1],[],[2,3],[4]] [] = [1,2,3,4]
fold_example3 = Refl

constfun : (x : ty) -> Nat -> ty
constfun x = \k => x

ftrue : Nat -> Bool
ftrue = constfun True

constfun_example1 : ftrue 0 = True
constfun_example1 = Refl

constfun_example2 : (constfun 5) 99 = 5
constfun_example2 = Refl

namespace Exercises
  fold_length : (l : List x) -> Nat
  fold_length l = fold (\_, n => S n) l 0

  test_fold_length1 : fold_length [4,7,0] = 3
  test_fold_length1 = Refl

  fold_length_correct : (l : List x) -> fold_length l = length l
  fold_length_correct [] = Refl
  fold_length_correct (x :: xs) = rewrite fold_length_correct xs in Refl

  prod_curry : (f : Prod x y -> z) -> (x_val : x) -> (y_val : y) -> z
  prod_curry f x_val y_val = f (PPair x_val y_val)

  prod_uncurry : (f : x -> y -> z) -> (p : Prod x y) -> z
  prod_uncurry f (PPair x_val y_val) = f x_val y_val

  uncurry_curry : (f : x -> y -> z) ->
                  (x_val : x) ->
                  (y_val : y) ->
                  prod_curry (prod_uncurry f) x_val y_val = f x_val y_val
  uncurry_curry f x_val y_val = Refl

  curry_uncurry : (f : Prod x y -> z) ->
                  (p : Prod x y) ->
                  prod_uncurry (prod_curry f) p = f p
  curry_uncurry f (PPair x y) = Refl
