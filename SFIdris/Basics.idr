module Basics

%default total

namespace Days
  public export
  data Day = 
      Monday
    | Tuesday
    | Wednesday 
    | Thursday 
    | Friday 
    | Saturday
    | Sunday

  %name Day day, day1, day2

  nextWeekday : Day -> Day
  nextWeekday Monday = Tuesday
  nextWeekday Tuesday = Wednesday
  nextWeekday Wednesday = Thursday
  nextWeekday Thursday = Friday
  nextWeekday Friday = Monday
  nextWeekday Saturday = Monday
  nextWeekday Sunday = Monday

  testNextWeekday : (nextWeekday (nextWeekday Saturday)) = Tuesday
  testNextWeekday = Refl

{-  
namespace Booleans
  %hide Bool

  data Bool : Type where
    True : Bool
    False : Bool
  
 
  not : (b : Bool) -> Bool
  not True = False
  not False = True
  
  andb : (b1 : Bool) -> (b2 : Bool) -> Bool
  andb True b2 = b2
  andb False b2 = False
  
  nandb : (b1: Bool) -> (b2 : Bool) -> Bool
  nandb = (not .) . andb
  
  test_nandb1 : (nandb True False) = True
  test_nandb1 = Refl
  
  test_nandb2 : (nandb False False) = True
  test_nandb2 = Refl
  
  test_nandb3 : (nandb False True) = True
  test_nandb3 = Refl
  
  test_nandb4 : (nandb True True) = False
  test_nandb4 = Refl
-}

namespace Numbers
  public export
  pred : (n : Nat) -> Nat
  pred Z = Z
  pred (S x) = x

  public export
  minusTwo : (n : Nat) -> Nat
  minusTwo Z = Z
  minusTwo (S Z) = Z
  minusTwo (S (S x)) = x

  public export
  evenb : (n : Nat) -> Bool
  evenb Z = True
  evenb (S Z) = False
  evenb (S (S x)) = evenb x

  public export
  oddb : (n : Nat) -> Bool
  oddb = not . evenb

  public export
  testOddb1 : oddb 1 = True
  testOddb1 = Refl

  public export
  testOddb2 : oddb 4 = False
  testOddb2 = Refl

namespace Playground2
  public export
  plus : (n, m : Nat) -> Nat
  plus Z m = m
  plus (S k) m = S (Playground2.plus k m)

  public export
  mult : (n, m : Nat) -> Nat
  mult Z m = Z
  mult (S k) m = Playground2.plus m (Playground2.mult k m)

  public export
  testMult1 : (Playground2.mult 3 3) = 9
  testMult1 = Refl
  
  {-
  minus : (n, m : Nat) -> Nat
  minus Z      _    = Z
  minus n      Z    = n
  minus (S k) (S j) = Playground2.minus k j
  -}

  public export
  exp : (base, power : Nat) -> Nat
  exp base Z = S Z
  exp base (S p) = Playground2.mult base (Playground2.exp base p)

  public export
  factorial : (n : Nat) -> Nat
  factorial Z = S Z
  factorial n@(S k) = n `Playground2.mult` factorial k

  public export
  testFactorial1 : factorial 3 = 6
  testFactorial1 = Refl

  public export
  testFactorial2 : factorial 5 = Playground2.mult 10 12
  testFactorial2 = Refl
  
  {-
  syntax [x] "+" [y] = Playground2.plus  x y;
  syntax [x] "-" [y] = Playground2.minus x y;
  syntax [x] "*" [y] = Playground2.mult  x y;
  
  (*) : Nat -> Nat -> Nat
  (*) = Playground2.mult
  
  (-) : Nat -> Nat -> Nat
  (-) = Playground2.minus
  
  (+) : Nat -> Nat -> Nat
  (+) = Playground2.plus
  
  infixl 9 *
  infixl 8 +, -
  
  
  
  (==) : (n, m : Nat) -> Bool
  (==)  Z     Z    = True
  (==)  Z    (S j) = False
  (==) (S k)  Z    = False
  (==) (S k) (S j) = k == j
  -}

public export
beq_nat : (n, m : Nat) -> Bool
beq_nat Z Z = True
beq_nat Z (S m) = False
beq_nat (S n) Z = False
beq_nat (S n) (S m) = beq_nat n m

public export
beq_nat_refl : (n : Nat) -> True = beq_nat n n
beq_nat_refl Z = Refl
beq_nat_refl (S k) =
  rewrite beq_nat_refl k in Refl
  
public export
eq_nat_refl : (n : Nat) -> True = (n == n)
eq_nat_refl Z = Refl
eq_nat_refl (S k) =
  let iH = eq_nat_refl k in
  rewrite iH in Refl

public export
plus_Z_n : (n : Nat) -> (0 + n) = n
plus_Z_n n = Refl
  
public export
plus_1_l : (n : Nat) -> (1 + n) = S n 
plus_1_l n = Refl
  
public export
mult_0_l : (n : Nat) -> (0 * n) = 0
mult_0_l n = Refl

public export
plus_id_example : (n, m: Nat) -> (n = m) -> n + n = m + m
plus_id_example n m prf = rewrite prf in Refl
  
public export
plus_id_excercise : (n, m, o : Nat) -> (n = m) -> (m = o) -> n + m = m + o
plus_id_excercise n m o prf prf1 = rewrite prf in rewrite prf1 in Refl
  
public export
mult_0_plus: (n, m : Nat) -> (0 + n) * m = n * (0 + m)
mult_0_plus n m = Refl

public export
mult_S_1: (n, m : Nat) -> (m = S n) -> (1 + n) * m = m * m
mult_S_1 n m prf = rewrite prf in Refl
  
public export
plus_1_neq_0 : (n : Nat) -> (n + 1) == 0 = False
plus_1_neq_0 Z = Refl
plus_1_neq_0 (S k) = Refl

public export
not_involutive : (b : Bool) -> not (not b) = b
not_involutive True = Refl
not_involutive False = Refl

public export
andb_t_t : (b = True) -> b = True
andb_t_t prf = rewrite prf in Refl

public export
andb_f_t : {b : Bool} -> (False = True) -> b = True
andb_f_t prf {b = False} = rewrite prf in Refl
andb_f_t prf {b = True} = Refl

public export
andb_true_elim_2 : (b, c : Bool) -> (b && c = True) -> c = True
andb_true_elim_2 False c = andb_f_t
andb_true_elim_2 True c = andb_t_t

public export
zero_nbeq_plus_1 : (n : Nat) -> 0 == (n + 1) = False
zero_nbeq_plus_1 Z = Refl
zero_nbeq_plus_1 (S k) = Refl

public export
identity_fn_applied_twice : (f : Bool -> Bool) ->
                            ((x : Bool) -> f x = x) ->
                            (b : Bool) -> f (f b) = b
identity_fn_applied_twice f g b = rewrite g b in rewrite g b in Refl

-- double negation proof
public export
dne : (b : Bool) -> not (not b) = b
dne False = Refl
dne True = Refl

public export
negation_fn_applied_twice : (f : Bool -> Bool) ->
                            ((x : Bool) -> f x = not x) ->
                            (b : Bool) -> f (f b) = b
negation_fn_applied_twice f g b = (cong f (g b) `trans` g (not b)) `trans` dne b
-- negation_fn_applied_twice f g b = 
--   rewrite g (f b) in rewrite g b in
--     case b of
--       True => Refl
--       False => Refl
