module Induction

import Basics as B
import Prelude.Interfaces
import Data.Nat

%hide Prelude.not

%default total

public export
plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z Z = Refl
plus_n_Z (S k) = 
  let inductiveHypothesis = plus_n_Z k in
    rewrite sym inductiveHypothesis in Refl

public export
minus_diag : (n : Nat) -> minus n n = 0
minus_diag Z = Refl
minus_diag (S k) = minus_diag k

public export
mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r Z = Refl
mult_0_r (S k) =
  let iH = mult_0_r k in
    rewrite iH in Refl
    
public export
plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm Z m = Refl
plus_n_Sm (S k) m =
  let iH = plus_n_Sm k m in 
  rewrite iH in 
  rewrite plus_n_Z k in Refl

public export
plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm Z m = rewrite sym (plus_n_Z m) in Refl
plus_comm (S k) m =
  let iH = plus_comm k m in
    rewrite iH in
    rewrite plus_n_Sm m k in Refl
    
public export
plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc Z m p = rewrite plus_comm m p in Refl
plus_assoc (S k) m p = 
  let iH = plus_assoc k m p in 
  rewrite iH in Refl

public export
double : (n : Nat) -> Nat
double Z = Z
double (S k) = S (S (double k))

public export
double_plus : (n : Nat) -> double n = n + n
double_plus Z = Refl
double_plus (S k) = 
  let iH = double_plus k in
    rewrite iH in
    rewrite plus_n_Sm k k in Refl

public export
evenb_S : (n : Nat) -> evenb (S n) = not (evenb n)
evenb_S Z = Refl
evenb_S (S k) =
  let iH = evenb_S k in
  rewrite iH in
  rewrite B.dne (evenb k) in Refl

-- apply arugments n and m to return proof for plus_comm
public export
plus_rearrange : (n, m, p, q : Nat) -> (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange n m p q = rewrite plus_comm n m in Refl

public export
plus_swap : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
plus_swap n m p =
  rewrite plus_assoc n m p in
  rewrite plus_comm n m in
  rewrite plus_assoc m n p in Refl

public export
plus_id : (n : Nat) -> n + 0 = n
plus_id Z = Refl
plus_id (S k) = rewrite plus_id k in Refl

public export
mult_id : (n : Nat) -> n * 1 = n
mult_id Z = Refl
mult_id (S k) = rewrite mult_id k in Refl

public export
mult_plus_n : (n, k : Nat) -> n + (n * k) = n * (S k)
mult_plus_n Z k = Refl
mult_plus_n (S j) k =
  rewrite sym (mult_plus_n j k) in
  rewrite plus_swap j k (j * k) in Refl
  
public export
mult_comm : (m, n : Nat) -> m * n = n * m
mult_comm Z n = rewrite mult_0_r n in Refl
mult_comm (S k) n =
  let iH = mult_comm k n in
  rewrite iH in
  rewrite mult_plus_n n k in Refl
  
public export
mult_1_l : (n : Nat) -> n * 1 = n
mult_1_l Z = Refl
mult_1_l (S k) = rewrite mult_1_l k in Refl

public export
mult_plus_distr_r : (n, m, p : Nat) -> (n + m) * p = (n * p) + (m * p)
mult_plus_distr_r Z m p = Refl
mult_plus_distr_r (S k) m p =
  rewrite mult_plus_distr_r k m p in
  rewrite plus_assoc p (k * p) (m * p) in Refl

public export
mult_assoc : (n, m, p : Nat) -> n * (m * p) = (n * m) * p
mult_assoc Z m p = Refl
mult_assoc (S k) m p =
  rewrite mult_assoc k m p in
  rewrite sym (mult_plus_distr_r m (k * m) p) in Refl
  
public export
beq_nat_refl : (n : Nat) -> True = n == n
beq_nat_refl Z = Refl
beq_nat_refl (S k) = rewrite Induction.beq_nat_refl k in Refl

public export
plus_swap' : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
plus_swap' n m p =
  rewrite plus_assoc n m p in
  rewrite plus_assoc m n p in
  replace (plus_comm n m) {p = \x => (n + m) + p = x + p} Refl

public export
data Bin : Type where
  O : Bin
  D : Bin -> Bin
  SD : Bin -> Bin
  
public export
incr_bin : Bin -> Bin
incr_bin O = SD O
incr_bin (D x) = SD x
incr_bin (SD x) = D (incr_bin x)

public export
bin_to_nat : Bin -> Nat
bin_to_nat O = 0
bin_to_nat (D x) = 2 * (bin_to_nat x)
bin_to_nat (SD x) = S (2 * (bin_to_nat x))

{-
  Incrementing a binary number and then converting it to a (unary)
  natural number yields the same result as first converting it to a
  natural number and then incrementing.
-}
public export
bin_to_nat_pres_incr : (b : Bin) -> S (bin_to_nat b) = bin_to_nat (incr_bin b)
bin_to_nat_pres_incr O = Refl
bin_to_nat_pres_incr (D x) = Refl
bin_to_nat_pres_incr (SD x) =
  let plusZ = \b => sym (plus_n_Z (bin_to_nat b)) in
  rewrite plusZ x in
  rewrite plusZ (incr_bin x) in
  rewrite sym (bin_to_nat_pres_incr x) in
  rewrite plus_n_Sm (bin_to_nat x) (bin_to_nat x) in Refl
  
public export
nat_to_bin : Nat -> Bin
nat_to_bin Z = O
nat_to_bin (S k) = incr_bin (nat_to_bin k)

public export
nat_bin_nat : (n : Nat) -> bin_to_nat (nat_to_bin n) = n
nat_bin_nat Z = Refl
nat_bin_nat (S k) =
  rewrite sym (bin_to_nat_pres_incr (nat_to_bin k)) in
  rewrite nat_bin_nat k in Refl
